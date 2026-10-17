const $effekt = {};
class Red_0 {
  constructor() {
    this.__tag = 0;
  }
  __reflect() {
    return { __tag: 0,__name: "Red",__data: [] };
  }
  __equals(other39870) {
    if (!other39870) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other39870.__tag))) {
      return false;
    }
    return true;
  }
}

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
function println_1(value_1,ks_2,k_1) {
  return b_show_1(value_1,ks_2,(v_showApp_1,ks_3) => {
    const v_r_1 = $effekt.println(v_showApp_1);
    return () => k_1(v_r_1,ks_3);
  });
}
function show_0(c_0,ks_6,k_4) {
  function b_k_0(ks_4,k_2) {
    return () => k_2("Green()",ks_4);
  }
  function b_k_1(ks_5,k_3) {
    return () => k_3("Blue()",ks_5);
  }
  return () => k_4("Red()",ks_6);
}
function main_0(ks_7,k_5) {
  return println_0(1,ks_7,(v_r_2,ks_8) => {
    const v_r_3 = $effekt.println("foo");
    return println_1(true,ks_8,(v_r_4,ks_9) =>
      println_1((1) === (2),ks_9,(v_r_5,ks_10) =>
        show_0(new Red_0(),ks_10,(v_r_6,ks_11) => {
          const v_r_7 = $effekt.println(v_r_6);
          return () => k_5(v_r_7,ks_11);
        })));
  });
}
function b_show_0(v_value_0,ks_12,k_6) {
  const v_ret_0 = '' + v_value_0;
  return () => k_6(v_ret_0,ks_12);
}
function b_show_1(v_value_1,ks_13,k_7) {
  if (v_value_1) {
    return () => k_7("true",ks_13);
  } else {
    return () => k_7("false",ks_13);
  }
}
(typeof module != "undefined" && module !== null ? module : {}).exports = $examples_pos_builtins = {
  main: () => RUN_TOPLEVEL(main_0)
};