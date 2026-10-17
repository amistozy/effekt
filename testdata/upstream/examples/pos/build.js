const $effekt = {};
class Tuple_0 {
  constructor(first_0,second_0) {
    this.__tag = 0;
    this.first_0 = first_0;
    this.second_0 = second_0;
  }
  __reflect() {
    return { __tag: 0,__name: "Tuple2",__data: [this.first_0,this.second_0] };
  }
  __equals(other41097) {
    if (!other41097) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other41097.__tag))) {
      return false;
    }
    if (!($effekt.equals(this.first_0,other41097.first_0))) {
      return false;
    }
    if (!($effekt.equals(this.second_0,other41097.second_0))) {
      return false;
    }
    return true;
  }
}
class Nil_0 {
  constructor() {
    this.__tag = 0;
  }
  __reflect() {
    return { __tag: 0,__name: "Nil",__data: [] };
  }
  __equals(other41098) {
    if (!other41098) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other41098.__tag))) {
      return false;
    }
    return true;
  }
}
class Cons_0 {
  constructor(head_0,tail_0) {
    this.__tag = 1;
    this.head_0 = head_0;
    this.tail_0 = tail_0;
  }
  __reflect() {
    return { __tag: 1,__name: "Cons",__data: [this.head_0,this.tail_0] };
  }
  __equals(other41099) {
    if (!other41099) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other41099.__tag))) {
      return false;
    }
    if (!($effekt.equals(this.head_0,other41099.head_0))) {
      return false;
    }
    if (!($effekt.equals(this.tail_0,other41099.tail_0))) {
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
function find_0(store_0,key_0,keyNotFound_0,ks_3,k_2) {
  function b_k_0(k_1,v_0,xs_0,ks_2) {
    if (k_1 === key_0) {
      return () => k_2(v_0,ks_2);
    } else {
      return find_0(xs_0,key_0,keyNotFound_0,ks_2,k_2);
    }
  }
  switch (store_0.__tag) {
    case 0: break;
    case 1:
      const head_1 = store_0.head_0;
      const xs_1 = store_0.tail_0;
      const k_3 = head_1.first_0;
      const v_1 = head_1.second_0;
      return () => b_k_0(k_3,v_1,xs_1,ks_3);
  }
  return keyNotFound_0.keyNotFound_1(key_0,ks_3,k_2);
}
function build_0(target_0,tasks_0,need_3,ks_11,k_10) {
  return RESET((b_p_0,ks_4,k_4) => {
    const tmp_tasks_0 = tasks_0;
    const need_0 = {
      need_1: (requestedKey_0,ks_5,k_5) =>
        SHIFT(b_p_0,(b_k_1,ks_6,k_6) => {
          function resume_0(v_a_0,ks_7) {
            return RESUME(b_k_1,(ks_8,k_7) => () => k_7(v_a_0,ks_8),ks_7,k_6);
          }
          return build_0(requestedKey_0,(k_8,need_2,need_2,ks_9,k_9) =>
            tasks_0(k_8,need_2,need_2,ks_9,k_9),ks_6,(v_r_1,ks_10) =>
            () => resume_0(v_r_1,ks_10));
        },ks_5,k_5)
    };
    return tasks_0(target_0,need_0,ks_4,k_4);
  },ks_11,k_10);
}
function memo_0(prog_0,need_6,ks_12,k_20) {
  const v_r_2 = new Nil_0();
  const store_1 = VAR(v_r_2,ks_12);
  return RESET((b_p_1,ks_13,k_11) => {
    const need_4 = {
      need_1: (key_1,ks_14,k_12) =>
        SHIFT(b_p_1,(b_k_2,ks_15,k_13) => {
          function resume_1(v_a_1,ks_17,k_15) {
            return RESUME(b_k_2,(ks_16,k_14) => () => k_14(v_a_1,ks_16),ks_17,k_15);
          }
          return RESET((b_p_2,ks_18,k_16) => {
            const keyNotFound_2 = {
              keyNotFound_1: (k_17,ks_19,k_18) =>
                SHIFT(b_p_2,(b_k_3,ks_20,k_19) =>
                  need_5.need_1(k_17,ks_20,(v_2,ks_21) => {
                    const v_s_0 = store_1.value;
                    store_1.set(new Cons_0(new Tuple_0(k_17,v_2),v_s_0));
                    return resume_1(v_2,ks_21,k_19);
                  }),ks_19,k_18)
            };
            const v_s_1 = store_1.value;
            return find_0(v_s_1,key_1,keyNotFound_2,keyNotFound_2,ks_18,(v_r_3,ks_22) =>
              resume_1(v_r_3,ks_22,k_16));
          },ks_15,k_13);
        },ks_14,k_12)
    };
    return prog_0(need_4,ks_13,k_11);
  },ks_12,(tmp_0,ks_23) => () => k_20(tmp_0,ks_23));
}
function supplyInput_0(store_2,prog_1,keyNotFound_4,ks_30,k_25) {
  return RESET((b_p_3,ks_24,k_21) => {
    const tmp_store_0 = store_2;
    const needInput_0 = {
      needInput_1: (key_2,ks_25,k_22) =>
        SHIFT(b_p_3,(b_k_4,ks_26,k_23) => {
          function resume_2(v_a_2,ks_27) {
            return RESUME(b_k_4,(ks_28,k_24) => () => k_24(v_a_2,ks_28),ks_27,k_23);
          }
          return find_0(tmp_store_0,key_2,keyNotFound_3,keyNotFound_3,ks_26,(v_r_4,ks_29) =>
            () => resume_2(v_r_4,ks_29));
        },ks_25,k_22)
    };
    return prog_1(needInput_0,ks_24,k_21);
  },ks_30,k_25);
}
function example_0(key_3,need_7,needInput_2,ks_31,k_26) {
  const v_r_5 = $effekt.println(key_3);
  if (key_3 === "B1") {
    return need_7.need_1("A1",ks_31,(v_r_6,ks_32) =>
      need_7.need_1("A2",ks_32,(v_r_7,ks_33) =>
        () => k_26((v_r_6 + v_r_7),ks_33)));
  } else if (key_3 === "B2") {
    return need_7.need_1("B1",ks_31,(v_r_8,ks_34) =>
      () => k_26((v_r_8 * (2)),ks_34));
  } else {
    return needInput_2.needInput_1(key_3,ks_31,k_26);
  }
}
function example_1(key_4,need_9,needInput_4,ks_35,k_27) {
  const v_r_9 = $effekt.println(key_4);
  if (key_4 === "B1") {
    return need_8.need_1("A1",ks_35,(v_r_10,ks_36) =>
      need_8.need_1("A2",ks_36,(v_r_11,ks_37) =>
        () => k_27((v_r_10 + v_r_11),ks_37)));
  } else if (key_4 === "B2") {
    return need_8.need_1("B1",ks_35,(v_r_12,ks_38) =>
      need_8.need_1("B1",ks_38,(v_r_13,ks_39) =>
        () => k_27((v_r_12 * v_r_13),ks_39)));
  } else {
    return needInput_3.needInput_1(key_4,ks_35,k_27);
  }
}
function main_0(ks_55,k_38) {
  return RESET((b_p_4,ks_40,k_28) => {
    const keyNotFound_5 = {
      keyNotFound_1: (key_5,ks_41,k_29) =>
        SHIFT(b_p_4,(b_k_5,ks_42,k_30) => {
          const v_r_14 = $effekt.println(("Key not found: " + key_5));
          return () => k_30(v_r_14,ks_42);
        },ks_41,k_29)
    };
    return supplyInput_0(new Cons_0(new Tuple_0("A1",10),new Cons_0(new Tuple_0("A2",20),new Nil_0())),(needInput_5,ks_43,k_31) =>
      build_0("B2",(key_6,need_10,ks_44,k_32) =>
        example_0(key_6,need_10,needInput_5,ks_44,k_32),ks_43,k_31),keyNotFound_5,ks_40,(result_0,ks_45) =>
      println_0(result_0,ks_45,(v_r_15,ks_46) => {
        const v_r_16 = $effekt.println("");
        return supplyInput_0(new Cons_0(new Tuple_0("A1",10),new Cons_0(new Tuple_0("A2",20),new Nil_0())),(needInput_6,ks_47,k_33) =>
          build_0("B2",(key_7,need_11,ks_48,k_34) =>
            example_1(key_7,need_11,needInput_6,ks_48,k_34),ks_47,k_33),keyNotFound_5,ks_46,(result_1,ks_49) =>
          println_0(result_1,ks_49,(v_r_17,ks_50) => {
            const v_r_18 = $effekt.println("");
            return supplyInput_0(new Cons_0(new Tuple_0("A1",10),new Cons_0(new Tuple_0("A2",20),new Nil_0())),(needInput_7,ks_51,k_35) =>
              build_0("B2",(key_8,need_12,ks_52,k_36) =>
                memo_0((need_13,ks_53,k_37) =>
                  example_1(key_8,need_13,needInput_7,ks_53,k_37),need_12,ks_52,k_36),ks_51,k_35),keyNotFound_5,ks_50,(result_2,ks_54) =>
              println_0(result_2,ks_54,k_28));
          }));
      }));
  },ks_55,k_38);
}
function b_show_0(v_value_0,ks_56,k_39) {
  const v_ret_0 = '' + v_value_0;
  return () => k_39(v_ret_0,ks_56);
}
(typeof module != "undefined" && module !== null ? module : {}).exports = $examples_pos_build = {
  main: () => RUN_TOPLEVEL(main_0)
};