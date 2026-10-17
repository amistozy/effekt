const $effekt = {};

// Sentinel: a node whose .value is Mem is the current root.
const Mem = null

// reusable buffer for rerooting
const _rerootPath = []

/**
 * A mutable reference inside an `Arena`.
 */
class Ref {
  constructor(v, s) {
    this.value = v;
    this.generation = s.generation;
    this.store = s;
  }

  set(v) {
    const s     = this.store;
    const r_gen = this.generation;
    const s_gen = s.generation;
    if (r_gen === s_gen) {
      this.value = v;
    } else {
      const root   = { value: Mem };
      s.root.value = { ref: this, value: this.value, generation: r_gen, root };

      s.root          = root;
      this.value      = v;
      this.generation = s_gen;
    }
  }
}

/**
 * A snapshottable arena: a bag of `Ref`s whose collective state can be
 * captured in O(1) and restored in O(#writes since capture).
 */
class Arena {
  constructor() {
    this.root       = { value: Mem };
    this.generation = 0;
  }

  /**
   * Allocate a new reference with initial value v.
   */
  fresh(v) {
    return new Ref(v, this);
  }

  /**
   * Region support (not implemented!).
   */
  newRegion() {
    return this;
  }
}

function snapshot(s) {
  if (s === null) return null
  const snap = { store: s, root: s.root, generation: s.generation }
  s.generation = s.generation + 1
  return snap
}

function reroot(target) {
  // 1. Walk from target toward the Mem node, collecting the path into `_rerootPath`
  _rerootPath.length = 0
  let cur = target
  while (cur.value !== Mem) {
    _rerootPath.push(cur)
    cur = cur.value.root
  }
  // cur is now Mem (the current root)

  // 2. Walk back from current root toward target,
  //    reverse each edge, restore each ref.
  for (let i = _rerootPath.length - 1; i >= 0; i--) {
    const node   = _rerootPath[i]
    const diff   = node.value // forward diff
    const r      = diff.ref
    cur.value    = { ref: r, value: r.value, generation: r.generation, root: node }
    r.value      = diff.value      // restore ref's old value
    r.generation = diff.generation //  ... and old generation
    node.value   = Mem
    cur          = node
  }

  // 3. Reclaim the path to reuse the buffer eagerly
  _rerootPath.length = 0
}

function restore(store, snap) {
  if (snap === null) return // nothing saved ~> nothing to restore
  if (snap.root.value !== Mem) {
    // fast path: continuation is resumed immediately with no writes in between
    reroot(snap.root)
    store.root = snap.root
  }
  store.generation = snap.generation + 1
}

// Common Runtime
// --------------
const TOPLEVEL_K = (x, ks) => { throw { computationIsDone: true, result: x } }
const TOPLEVEL_KS = { stack: null, prompt: Symbol("toplevel"), arena: null, rest: null }

// The first variable in a scope creates its arena; until then `ks.arena` is null.
function VAR(init, ks) {
  const arena = ks.arena !== null ? ks.arena : (ks.arena = new Arena())
  return arena.fresh(init)
}

function REGION(ks) {
  const arena = ks.arena !== null ? ks.arena : (ks.arena = new Arena())
  return arena.newRegion()
}

function THUNK(f) {
  f.thunk = true
  return f
}

function CAPTURE(body) {
  return (ks, k) => {
    const res = body(x => TRAMPOLINE(() => k(x, ks)))
    if (typeof res === "function") return res
    else throw { computationIsDone: true, result: $effekt.unit }
  }
}

const RETURN = (x, ks) => ks.rest.stack(x, ks.rest)

// HANDLE(ks, ks, (p, ks, k) => { STMT })
function RESET(prog, ks, k) {
  const prompt = Symbol(); // gensym
  const rest = { stack: k, prompt: ks.prompt, arena: ks.arena, rest: ks.rest }
  return prog(prompt, { stack: null, prompt, arena: null, rest }, RETURN)
}

function SHIFT(p, body, ks, k) {

  // TODO avoid constructing this object
  let meta = { stack: k, prompt: ks.prompt, arena: ks.arena, rest: ks.rest }
  let cont = null

  while (!!meta && meta.prompt !== p) {
    let store = meta.arena
    cont = { stack: meta.stack, prompt: meta.prompt, arena: store, backup: snapshot(store), rest: cont }
    meta = meta.rest
  }
  if (!meta) { throw `Prompt not found ${p}` }

  // package the prompt itself
  let store = meta.arena
  cont = { stack: meta.stack, prompt: meta.prompt, arena: store, backup: snapshot(store), rest: cont }
  meta = meta.rest

  const k1 = meta.stack
  meta.stack = null
  return body(cont, meta, k1)
}

// Rewind stack `cont` back onto `k` :: `ks` and resume with c
function RESUME(cont, c, ks, k) {
  let meta = { stack: k, prompt: ks.prompt, arena: ks.arena, rest: ks.rest }
  let toRewind = cont
  while (!!toRewind) {
    restore(toRewind.arena, toRewind.backup)
    meta = { stack: toRewind.stack, prompt: toRewind.prompt, arena: toRewind.arena, rest: meta }
    toRewind = toRewind.rest
  }

  const k1 = meta.stack // TODO instead copy meta here, like elsewhere?
  meta.stack = null
  return () => c(meta, k1)
}

function RUN_TOPLEVEL(comp) {
  try {
    let a = comp(TOPLEVEL_KS, TOPLEVEL_K)
    while (true) { a = a() }
  } catch (e) {
    if (e.computationIsDone) return e.result
    else throw e
  }
}

// trampolines the given computation (like RUN_TOPLEVEL, but doesn't provide continuations)
function TRAMPOLINE(comp) {
  let a = comp;
  try {
    while (true) {
      a = a()
    }
  } catch (e) {
    if (e.computationIsDone) return e.result
    else throw e
  }
}

// keeps the current trampoline going and dispatches the given task
function RUN(task) {
  return () => task(TOPLEVEL_KS, TOPLEVEL_K)
}

// aborts the current continuation
function ABORT(value) {
  throw { computationIsDone: true, result: value }
}


// "Public API" used in FFI
// ------------------------

/**
 * Captures the current continuation as a WHOLE and makes it available
 * as argument to the passed body. For example:
 *
 *   $effekt.capture(k => ... k(42) ...)
 *
 * The body
 *
 *   $effekt.capture(k => >>> ... <<<)
 *
 * conceptually runs on the _native_ JS call stack. You can call JS functions,
 * like `setTimeout` etc., but you are not expected or required to return an
 * Effekt value like `$effekt.unit`. If you want to run an Effekt computation
 * like in `io::spawn`, you can use `$effekt.run`.
 *
 * Advanced usage details:
 *
 * The value returned by the function passed to `capture` returns
 * - a function: the returned function will be passed to the
 *   Effekt runtime, which performs trampolining.
 *   In this case, the Effekt runtime will keep running, though the
 *   continuation has been removed.
 *
 * - another value (like `undefined`): the Effekt runtime will terminate.
 */
$effekt.capture = CAPTURE

/**
 * Used to call Effekt function arguments in the JS FFI, like in `io::spawn`.
 *
 * Requires an active Effekt runtime (trampoline).
 */
$effekt.run = RUN

/**
 * Used to call Effekt function arguments in the JS FFI, like in `network::listen`.
 *
 * This function should be used when _no_ Effekt runtime is available. For instance,
 * in callbacks passed to the NodeJS eventloop.
 *
 * If a runtime is available, use `$effekt.run`, instead.
 */
$effekt.runToplevel = RUN_TOPLEVEL

$effekt.show = function(obj) {
  if (!!obj && !!obj.__reflect) {
    const meta = obj.__reflect()
    return meta.__name + "(" + meta.__data.map($effekt.show).join(", ") + ")"
  }
  else if (!!obj && obj.__unit) {
    return "()";
  } else {
    return "" + obj;
  }
}

$effekt.equals = function(obj1, obj2) {
  if (!!obj1.__equals) {
    return obj1.__equals(obj2)
  } else {
    return (obj1.__unit && obj2.__unit) || (obj1 === obj2);
  }
}

function compare$prim(n1, n2) {
  if (n1 == n2) { return 0; }
  else if (n1 > n2) { return 1; }
  else { return -1; }
}

$effekt.compare = function(obj1, obj2) {
  if ($effekt.equals(obj1, obj2)) { return 0; }

  if (!!obj1 && !!obj2) {
    if (!!obj1.__reflect && !!obj2.__reflect) {
      const tagOrdering = compare$prim(obj1.__tag, obj2.__tag)
      if (tagOrdering != 0) { return tagOrdering; }

      const meta1 = obj1.__reflect().__data
      const meta2 = obj2.__reflect().__data

      const lengthOrdering = compare$prim(meta1.length, meta2.length)
      if (lengthOrdering != 0) { return lengthOrdering; }

      for (let i = 0; i < meta1.length; i++) {
        const contentOrdering = $effekt.compare(meta1[i], meta2[i])
        if (contentOrdering != 0) { return contentOrdering; }
      }

      return 0;
    }
  }

  return compare$prim(obj1, obj2);
}

$effekt.println = function println$impl(str) {
  console.log(str); return $effekt.unit;
}

$effekt.print = function println$impl(str) {
  process.stdout.write(str); return $effekt.unit;
}

$effekt.unit = { __unit: true }

$effekt.unreachable = function() { throw "should not be reachable!" }

$effekt.hole = function(pos) { throw pos + " not implemented yet" }


$effekt.readln = function readln$impl(callback) {
  const readline = require('node:readline').createInterface({
    input: process.stdin,
    output: process.stdout,
  });
  readline.question('', (answer) => {
    readline.close();
    callback(answer);
  });
}


  function array$get(arr, index) {
    if (index < 0 || index >= arr.length) throw 'Index out of bounds';
    return arr[index];
  }


  function array$set(arr, index, value) {
    if (index < 0 || index >= arr.length) throw 'Index out of bounds';
    arr[index] = value;
    return $effekt.unit
  }

// extern type ByteArray = Uint8Array

  function bytearray$get(arr, index) {
    if (index < 0 || index >= arr.length) throw 'Index out of bounds';
    return arr[index];
  }


  function bytearray$copy(src, srcOff, dst, dstOff, n) {
    // for small `n`, it's faster to copy manually to avoid allocating `subarray`
    if (n < 40) {
      if (srcOff < dstOff) {
        for (let i = n - 1; i >= 0; --i) dst[dstOff + i] = src[srcOff + i];
      } else {
        for (let i = 0; i < n; ++i) dst[dstOff + i] = src[srcOff + i];
      }
    } else {
      // safe: `set` clones the source region first when both share a buffer
      dst.set(src.subarray(srcOff, srcOff + n), dstOff);
    }
    return $effekt.unit;
  }

  function bytearray$set(bytes, index, value) {
    bytes[index] = value;
    return $effekt.unit;
  }

  function bytearray$compare(arr1, arr2) {
    const len = Math.min(arr1.length, arr2.length);

    for (let i = 0; i < len; i++) {
      if (arr1[i] !== arr2[i]) {
        return arr1[i] < arr2[i] ? -1 : 1;
      }
    }

    if (arr1.length !== arr2.length) {
      return arr1.length < arr2.length ? -1 : 1;
    } else {
      return 0;
    }
  }


  function set$impl(ref, value) {
    ref.value = value;
    return $effekt.unit;
  }

function println_0(value_0,ks_0,k_0) {
  return b_show_0(value_0,ks_0,(v_showApp_0,ks_1) => {
    const v_r_0 = $effekt.println(v_showApp_0);
    return () => k_0(v_r_0,ks_1);
  });
}
function loop_0(action_0,stop_2,ks_7,k_5) {
  return RESET((b_p_0,ks_2,k_1) => {
    const stop_0 = {
      stop_1: (ks_3,k_2) =>
        SHIFT(b_p_0,(b_k_0,ks_4,k_3) => () => k_3($effekt.unit,ks_4),ks_3,k_2)
    };
    const tmp_action_0 = action_0;
    function go_0(ks_5,k_4) {
      return action_0(stop_0,ks_5,(v_r_1,ks_6) => go_0(ks_6,k_4));
    }
    return go_0(ks_2,k_1);
  },ks_7,k_5);
}
function decodeChar_0(stop_3,next_0,ks_8,k_6) {
  return next_0.next_1(stop_3,ks_8,(v_r_2,ks_9) => {
    if (((v_r_2) < (128))) {
      return () => k_6((v_r_2),ks_9);
    } else if (((v_r_2) < (224))) {
      return next_0.next_1(stop_3,ks_9,(v_r_3,ks_10) =>
        () => k_6((((((((v_r_2) & (31))) << (6))) | (((v_r_3) & (63))))),ks_10));
    } else if (((v_r_2) < (240))) {
      return next_0.next_1(stop_3,ks_9,(v_r_4,ks_11) =>
        next_0.next_1(stop_3,ks_11,(v_r_5,ks_12) =>
          () =>
            k_6((((((((((v_r_2) & (15))) << (12))) | (((((v_r_4) & (63))) << (6))))) | (((v_r_5) & (63))))),ks_12)));
    } else {
      return next_0.next_1(stop_3,ks_9,(v_r_6,ks_13) =>
        next_0.next_1(stop_3,ks_13,(v_r_7,ks_14) =>
          next_0.next_1(stop_3,ks_14,(v_r_8,ks_15) =>
            () =>
              k_6((((((((((((v_r_2) & (7))) << (18))) | (((((v_r_6) & (63))) << (12))))) | (((((v_r_7) & (63))) << (6))))) | (((v_r_8) & (63))))),ks_15))));
    }
  });
}
function decodeUTF_0(reader_0,next_4,next_2,ks_22,k_13) {
  return RESET((b_p_1,ks_16,k_7) => {
    const tmp_next_0 = next_2;
    const next_3 = {
      next_1: (b_g_0,ks_17,k_8) =>
        SHIFT(b_p_1,(b_k_1,ks_18,k_9) => {
          function resume_0(b_h_0,ks_20,k_11) {
            return RESUME(b_k_1,(ks_19,k_10) => b_h_0(b_g_0,ks_19,k_10),ks_20,k_11);
          }
          return resume_0((stop_4,stop_4,ks_21,k_12) =>
            decodeChar_0(stop_4,next_2,stop_4,next_2,ks_21,k_12),ks_18,k_9);
        },ks_17,k_8)
    };
    return reader_0(next_3,ks_16,k_7);
  },ks_22,k_13);
}
function feed_0(bytes_0,driver_0,next_6,ks_23,k_20) {
  const v_r_9 = 0;
  const i_0 = VAR(v_r_9,ks_23);
  return RESET((b_p_2,ks_24,k_14) => {
    const tmp_bytes_0 = bytes_0;
    const next_5 = {
      next_1: (b_g_1,ks_25,k_15) =>
        SHIFT(b_p_2,(b_k_2,ks_26,k_16) => {
          function resume_1(b_h_1,ks_28,k_18) {
            return RESUME(b_k_2,(ks_27,k_17) => b_h_1(b_g_1,ks_27,k_17),ks_28,k_18);
          }
          return resume_1((stop_5,stop_5,ks_29,k_19) => {
            const v_s_0 = i_0.value;
            if ((v_s_0 < (tmp_bytes_0.length))) {
              const v_s_1 = i_0.value;
              i_0.set((v_s_1 + (1)));
              const v_r_10 = bytearray$get(tmp_bytes_0, v_s_1);
              return () => k_19(v_r_10,ks_29);
            } else {
              return stop_5.stop_1(ks_29,k_19);
            }
          },ks_26,k_16);
        },ks_25,k_15)
    };
    return driver_0(next_5,ks_24,k_14);
  },ks_23,(tmp_0,ks_30) => () => k_20(tmp_0,ks_30));
}
function feed_1(string_0,driver_1,ks_33,k_23) {
  return feed_0((new TextEncoder().encode(string_0)),(next_7,ks_31,k_21) =>
    decodeUTF_0((next_8,ks_32,k_22) => driver_1(next_8,ks_32,k_22),next_7,ks_31,k_21),ks_33,k_23);
}
function parse_0(s_0,ks_38,k_26) {
  return feed_1(s_0,(next_9,ks_34,k_24) => {
    const v_r_11 = 0;
    const acc_0 = VAR(v_r_11,ks_34);
    return loop_0((stop_6,ks_35,k_25) => {
      const v_s_2 = acc_0.value;
      return next_9.next_1(stop_6,ks_35,(v_r_12,ks_36) => {
        acc_0.set(((((10) * v_s_2)) + (((v_r_12) - (48)))));
        return () => k_25($effekt.unit,ks_36);
      });
    },ks_34,(v_r_13,ks_37) => {
      const v_s_3 = acc_0.value;
      return () => k_24(v_s_3,ks_37);
    });
  },ks_38,k_26);
}
function main_0(ks_39,k_27) {
  return parse_0("12345",ks_39,(v_r_14,ks_40) => println_0(v_r_14,ks_40,k_27));
}
function b_show_0(v_value_0,ks_41,k_28) {
  const v_ret_0 = '' + v_value_0;
  return () => k_28(v_ret_0,ks_41);
}
(typeof module != "undefined" && module !== null ? module : {}).exports = $abort_past_joinpoint = {
  main: () => RUN_TOPLEVEL(main_0)
};