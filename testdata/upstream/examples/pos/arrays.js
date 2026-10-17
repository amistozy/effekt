const $effekt = {};
class Nil_0 {
  constructor() {
    this.__tag = 0;
  }
  __reflect() {
    return { __tag: 0,__name: "Nil",__data: [] };
  }
  __equals(other40108) {
    if (!other40108) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other40108.__tag))) {
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
  __equals(other40109) {
    if (!other40109) {
      return false;
    }
    if (!($effekt.equals(this.__tag,other40109.__tag))) {
      return false;
    }
    if (!($effekt.equals(this.head_0,other40109.head_0))) {
      return false;
    }
    if (!($effekt.equals(this.tail_0,other40109.tail_0))) {
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

// extern type ArrayT = Array

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

function each_0(start_0,end_0,action_0,ks_2,k_1) {
  const tmp_end_0 = end_0;
  const tmp_action_0 = action_0;
  function loop_0(i_0,ks_0,k_0) {
    if ((i_0 < tmp_end_0)) {
      return action_0(i_0,ks_0,(v_r_0,ks_1) => loop_0((i_0 + (1)),ks_1,k_0));
    } else {
      return () => k_0($effekt.unit,ks_0);
    }
  }
  return loop_0(start_0,ks_2,k_1);
}
function foreach_0(l_0,f_0,ks_5,k_2) {
  function b_k_0(head_1,tail_1,ks_3) {
    return f_0(head_1,ks_3,(v_r_1,ks_4) => foreach_0(tail_1,f_0,ks_4,k_2));
  }
  switch (l_0.__tag) {
    case 0: break;
    case 1:
      const head_2 = l_0.head_0;
      const tail_2 = l_0.tail_0;
      return () => b_k_0(head_2,tail_2,ks_5);
  }
  return () => k_2($effekt.unit,ks_5);
}
function foreachIndex_0(list_0,f_1,ks_9,k_4) {
  const tmp_f_0 = f_1;
  function loop_1(index_0,remainder_0,ks_8,k_3) {
    function b_k_1(head_3,tail_3,ks_6) {
      return f_1(index_0,head_3,ks_6,(v_r_2,ks_7) =>
        loop_1((index_0 + (1)),tail_3,ks_7,k_3));
    }
    switch (remainder_0.__tag) {
      case 0: break;
      case 1:
        const head_4 = remainder_0.head_0;
        const tail_4 = remainder_0.tail_0;
        return () => b_k_1(head_4,tail_4,ks_8);
    }
    return () => k_3($effekt.unit,ks_8);
  }
  return loop_1(0,list_0,ks_9,k_4);
}
function size_0(l_1,ks_10,k_6) {
  const v_r_3 = 0;
  const n_0 = VAR(v_r_3,ks_10);
  return foreach_0(l_1,(_0,ks_11,k_5) => {
    const v_s_0 = n_0.value;
    n_0.set((v_s_0 + (1)));
    return () => k_5($effekt.unit,ks_11);
  },ks_10,(v_r_4,ks_12) => {
    const v_s_1 = n_0.value;
    return () => k_6(v_s_1,ks_12);
  });
}
function fill_0(arr_0,filler_0,ks_14,k_8) {
  const tmp_arr_0 = arr_0;
  const tmp_filler_0 = filler_0;
  function go_0(i_1,ks_13,k_7) {
    go_0: while (true) {
      if ((i_1 < (tmp_arr_0.length))) {
        const v_r_5 = array$set(tmp_arr_0, i_1, tmp_filler_0);
        /* prepare call */
        const tmp_i_0 = i_1;
        i_1 = (tmp_i_0 + (1));
        continue go_0;
      } else {
        return () => k_7($effekt.unit,ks_13);
      }
    }
  }
  return go_0(0,ks_14,k_8);
}
function array_0(size_1,init_0,ks_15,k_9) {
  const v_r_6 = (new Array(size_1));
  return fill_0(v_r_6,init_0,ks_15,(v_r_7,ks_16) => () => k_9(v_r_6,ks_16));
}
function fromList_0(list_1,ks_17,k_11) {
  return size_0(list_1,ks_17,(listSize_0,ks_18) => {
    const v_r_8 = (new Array(listSize_0));
    return foreachIndex_0(list_1,(i_2,head_5,ks_19,k_10) => {
      const v_r_9 = array$set(v_r_8, i_2, head_5);
      return () => k_10(v_r_9,ks_19);
    },ks_18,(v_r_10,ks_20) => () => k_11(v_r_8,ks_20));
  });
}
function build_0(size_2,index_1,ks_23,k_13) {
  const v_r_11 = (new Array(size_2));
  return each_0(0,size_2,(i_3,ks_21,k_12) =>
    index_1(i_3,ks_21,(v_r_12,ks_22) => {
      const v_r_13 = array$set(v_r_11, i_3, v_r_12);
      return () => k_12(v_r_13,ks_22);
    }),ks_23,(v_r_14,ks_24) => () => k_13(v_r_11,ks_24));
}
function foreachIndex_1(arr_1,action_1,ks_26,k_15) {
  return each_0(0,arr_1.length,(i_4,ks_25,k_14) => {
    const v_r_15 = array$get(arr_1, i_4);
    return action_1(i_4,v_r_15,ks_25,k_14);
  },ks_26,k_15);
}
function showBuiltin_0(arr_2,showA_0,ks_27,k_17) {
  const v_r_16 = "Array(";
  const output_0 = VAR(v_r_16,ks_27);
  return foreachIndex_1(arr_2,(index_2,a_0,ks_28,k_16) => {
    if (index_2 === (((arr_2.length) - (1)))) {
      const v_s_2 = output_0.value;
      return showA_0(a_0,ks_28,(v_r_17,ks_29) => {
        output_0.set(v_s_2 + v_r_17);
        return () => k_16($effekt.unit,ks_29);
      });
    } else {
      const v_s_3 = output_0.value;
      return showA_0(a_0,ks_28,(v_r_18,ks_30) => {
        output_0.set((v_s_3 + v_r_18) + ", ");
        return () => k_16($effekt.unit,ks_30);
      });
    }
  },ks_27,(v_r_19,ks_31) => {
    const v_s_4 = output_0.value;
    output_0.set(v_s_4 + ")");
    const v_s_5 = output_0.value;
    return () => k_17(v_s_5,ks_31);
  });
}
function showBuiltin_1(l_2,ks_34,k_19) {
  return showBuiltin_0(l_2,(e_0,ks_32,k_18) =>
    b_show_0(e_0,ks_32,(v_showApp_0,ks_33) => () => k_18(v_showApp_0,ks_33)),ks_34,k_19);
}
function showBuiltin_2(l_3,ks_36,k_21) {
  return showBuiltin_0(l_3,(e_1,ks_35,k_20) => () => k_20(e_1,ks_35),ks_36,k_21);
}
function println_0(l_4,ks_37,k_22) {
  return showBuiltin_1(l_4,ks_37,(v_r_20,ks_38) => {
    const v_r_21 = $effekt.println(v_r_20);
    return () => k_22(v_r_21,ks_38);
  });
}
function println_1(l_5,ks_39,k_23) {
  return showBuiltin_2(l_5,ks_39,(v_r_22,ks_40) => {
    const v_r_23 = $effekt.println(v_r_22);
    return () => k_23(v_r_23,ks_40);
  });
}
function main_0(ks_41,k_25) {
  return array_0(5,"",ks_41,(arr_3,ks_42) => {
    const v_r_24 = array$set(arr_3, (0), "hello");
    const v_r_25 = array$set(arr_3, (2), "world");
    const v_r_26 = array$get(arr_3, (0));
    const v_r_27 = $effekt.println(v_r_26);
    const v_r_28 = array$get(arr_3, (2));
    const v_r_29 = $effekt.println(v_r_28);
    return array_0(4,"Hello World",ks_42,(arrWithVals_0,ks_43) =>
      println_1(arrWithVals_0,ks_43,(v_r_30,ks_44) =>
        build_0(5,(i_5,ks_45,k_24) => () => k_24(i_5,ks_45),ks_44,(arrByF_0,ks_46) =>
          println_0(arrByF_0,ks_46,(v_r_31,ks_47) =>
            fromList_0(new Cons_0(1,new Cons_0(5,new Cons_0(17,new Nil_0()))),ks_47,(v_r_32,ks_48) => {
              const arrByList_0 = VAR(v_r_32,ks_48);
              const v_s_6 = arrByList_0.value;
              return println_0(v_s_6,ks_48,(tmp_0,ks_49) =>
                () => k_25(tmp_0,ks_49));
            })))));
  });
}
function b_show_0(v_value_0,ks_50,k_26) {
  const v_ret_0 = '' + v_value_0;
  return () => k_26(v_ret_0,ks_50);
}
(typeof module != "undefined" && module !== null ? module : {}).exports = $examples_pos_arrays = {
  main: () => RUN_TOPLEVEL(main_0)
};