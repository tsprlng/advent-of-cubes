"use strict";
(function(){
var addMeshFromQuads = function(quads, color){
	postMessage({quads: quads, color: color});
};
var wandow = self;
var __haste_prog_id = 'a6f2aea0fb47e658fdd96de440e65e2d4b9114ff952cd5253ba591450bcbe80a';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof wandow === 'undefined' && typeof global !== 'undefined') wandow = global;
wandow['__haste_crypto'] = wandow.crypto || wandow.msCrypto;
if(wandow['__haste_crypto'] && !wandow['__haste_crypto'].subtle && wandow.crypto.webkitSubtle) {
    wandow['__haste_crypto'].subtle = wandow.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!wandow) {
    var wandow = {};
}
wandow['Haste'] = Haste;
wandow['A'] = A;
wandow['E'] = E;
wandow['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

wandow['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = wandow.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new wandow[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new wandow[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

wandow['toABle'] = toABHost;
wandow['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    wandow['toABle'] = toABSwap;
    wandow['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
wandow['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

wandow['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
wandow['newArr'] = newArr;
wandow['newByteArr'] = newByteArr;
wandow['wrapByteArr'] = wrapByteArr;
wandow['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
wandow.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    wandow.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return wandow.__hs_spt[key];
}

var _0=function(_1){return new F(function(){return __lst2arr(E(_1));});},_2=function(_3){return E(_3);},_4=new T2(0,_2,_0),_5=__Z,_6=function(_7,_8){var _9=E(_8);return (_9._==0)?__Z:new T2(1,new T(function(){return B(A1(_7,_9.a));}),new T(function(){return B(_6(_7,_9.b));}));},_a=function(_b){return E(E(_b).a);},_c=function(_d,_e,_f,_g,_h,_i){var _j=__lst2arr(B(_6(_2,new T2(1,new T(function(){return B(A2(_a,_d,_g));}),new T2(1,new T(function(){return B(A2(_a,_e,_h));}),new T2(1,new T(function(){return B(A2(_a,_f,_i));}),_5))))));return E(_j);},_k=function(_l,_m,_n,_o){var _p=E(_o);return new F(function(){return _c(_l,_m,_n,_p.a,_p.b,_p.c);});},_q=function(_r,_s,_t,_u){var _v=__lst2arr(B(_6(function(_w){return new F(function(){return _k(_r,_s,_t,_w);});},_u)));return E(_v);},_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return B(_x(_A.b,_z));}));},_B=new T1(0,1),_C=function(_D,_E){while(1){var _F=E(_D);if(!_F._){var _G=_F.a,_H=E(_E);if(!_H._){var _I=_H.a,_J=addC(_G,_I);if(!E(_J.b)){return new T1(0,_J.a);}else{_D=new T1(1,I_fromInt(_G));_E=new T1(1,I_fromInt(_I));continue;}}else{_D=new T1(1,I_fromInt(_G));_E=_H;continue;}}else{var _K=E(_E);if(!_K._){_D=_F;_E=new T1(1,I_fromInt(_K.a));continue;}else{return new T1(1,I_add(_F.a,_K.a));}}}},_L=function(_M,_N){var _O=E(_M);return new T2(0,_O,new T(function(){var _P=B(_L(B(_C(_O,_N)),_N));return new T2(1,_P.a,_P.b);}));},_Q=function(_R){var _S=B(_L(_R,_B));return new T2(1,_S.a,_S.b);},_T=function(_U,_V){while(1){var _W=E(_U);if(!_W._){var _X=_W.a,_Y=E(_V);if(!_Y._){var _Z=_Y.a,_10=subC(_X,_Z);if(!E(_10.b)){return new T1(0,_10.a);}else{_U=new T1(1,I_fromInt(_X));_V=new T1(1,I_fromInt(_Z));continue;}}else{_U=new T1(1,I_fromInt(_X));_V=_Y;continue;}}else{var _11=E(_V);if(!_11._){_U=_W;_V=new T1(1,I_fromInt(_11.a));continue;}else{return new T1(1,I_sub(_W.a,_11.a));}}}},_12=function(_13,_14){var _15=B(_L(_13,new T(function(){return B(_T(_14,_13));})));return new T2(1,_15.a,_15.b);},_16=new T1(0,0),_17=function(_18,_19){var _1a=E(_18);if(!_1a._){var _1b=_1a.a,_1c=E(_19);return (_1c._==0)?_1b>=_1c.a:I_compareInt(_1c.a,_1b)<=0;}else{var _1d=_1a.a,_1e=E(_19);return (_1e._==0)?I_compareInt(_1d,_1e.a)>=0:I_compare(_1d,_1e.a)>=0;}},_1f=function(_1g,_1h){var _1i=E(_1g);if(!_1i._){var _1j=_1i.a,_1k=E(_1h);return (_1k._==0)?_1j>_1k.a:I_compareInt(_1k.a,_1j)<0;}else{var _1l=_1i.a,_1m=E(_1h);return (_1m._==0)?I_compareInt(_1l,_1m.a)>0:I_compare(_1l,_1m.a)>0;}},_1n=function(_1o,_1p){var _1q=E(_1o);if(!_1q._){var _1r=_1q.a,_1s=E(_1p);return (_1s._==0)?_1r<_1s.a:I_compareInt(_1s.a,_1r)>0;}else{var _1t=_1q.a,_1u=E(_1p);return (_1u._==0)?I_compareInt(_1t,_1u.a)<0:I_compare(_1t,_1u.a)<0;}},_1v=function(_1w,_1x,_1y){if(!B(_17(_1x,_16))){var _1z=function(_1A){return (!B(_1n(_1A,_1y)))?new T2(1,_1A,new T(function(){return B(_1z(B(_C(_1A,_1x))));})):__Z;};return new F(function(){return _1z(_1w);});}else{var _1B=function(_1C){return (!B(_1f(_1C,_1y)))?new T2(1,_1C,new T(function(){return B(_1B(B(_C(_1C,_1x))));})):__Z;};return new F(function(){return _1B(_1w);});}},_1D=function(_1E,_1F,_1G){return new F(function(){return _1v(_1E,B(_T(_1F,_1E)),_1G);});},_1H=function(_1I,_1J){return new F(function(){return _1v(_1I,_B,_1J);});},_1K=function(_1L){var _1M=E(_1L);if(!_1M._){return E(_1M.a);}else{return new F(function(){return I_toInt(_1M.a);});}},_1N=function(_1O){return new F(function(){return _1K(_1O);});},_1P=function(_1Q){return new F(function(){return _T(_1Q,_B);});},_1R=function(_1S){return new F(function(){return _C(_1S,_B);});},_1T=function(_1U){return new T1(0,_1U);},_1V=function(_1W){return new F(function(){return _1T(E(_1W));});},_1X={_:0,a:_1R,b:_1P,c:_1V,d:_1N,e:_Q,f:_12,g:_1H,h:_1D},_1Y=function(_1Z,_20){if(_1Z<=0){if(_1Z>=0){return new F(function(){return quot(_1Z,_20);});}else{if(_20<=0){return new F(function(){return quot(_1Z,_20);});}else{return quot(_1Z+1|0,_20)-1|0;}}}else{if(_20>=0){if(_1Z>=0){return new F(function(){return quot(_1Z,_20);});}else{if(_20<=0){return new F(function(){return quot(_1Z,_20);});}else{return quot(_1Z+1|0,_20)-1|0;}}}else{return quot(_1Z-1|0,_20)-1|0;}}},_21=function(_22,_23){while(1){var _24=E(_22);if(!_24._){var _25=E(_24.a);if(_25==( -2147483648)){_22=new T1(1,I_fromInt( -2147483648));continue;}else{var _26=E(_23);if(!_26._){return new T1(0,B(_1Y(_25,_26.a)));}else{_22=new T1(1,I_fromInt(_25));_23=_26;continue;}}}else{var _27=_24.a,_28=E(_23);return (_28._==0)?new T1(1,I_div(_27,I_fromInt(_28.a))):new T1(1,I_div(_27,_28.a));}}},_29=new T(function(){return B(unCStr("base"));}),_2a=new T(function(){return B(unCStr("GHC.Exception"));}),_2b=new T(function(){return B(unCStr("ArithException"));}),_2c=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_29,_2a,_2b),_2d=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2c,_5,_5),_2e=function(_2f){return E(_2d);},_2g=function(_2h){return E(E(_2h).a);},_2i=function(_2j,_2k,_2l){var _2m=B(A1(_2j,_)),_2n=B(A1(_2k,_)),_2o=hs_eqWord64(_2m.a,_2n.a);if(!_2o){return __Z;}else{var _2p=hs_eqWord64(_2m.b,_2n.b);return (!_2p)?__Z:new T1(1,_2l);}},_2q=function(_2r){var _2s=E(_2r);return new F(function(){return _2i(B(_2g(_2s.a)),_2e,_2s.b);});},_2t=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2u=new T(function(){return B(unCStr("denormal"));}),_2v=new T(function(){return B(unCStr("divide by zero"));}),_2w=new T(function(){return B(unCStr("loss of precision"));}),_2x=new T(function(){return B(unCStr("arithmetic underflow"));}),_2y=new T(function(){return B(unCStr("arithmetic overflow"));}),_2z=function(_2A,_2B){switch(E(_2A)){case 0:return new F(function(){return _x(_2y,_2B);});break;case 1:return new F(function(){return _x(_2x,_2B);});break;case 2:return new F(function(){return _x(_2w,_2B);});break;case 3:return new F(function(){return _x(_2v,_2B);});break;case 4:return new F(function(){return _x(_2u,_2B);});break;default:return new F(function(){return _x(_2t,_2B);});}},_2C=function(_2D){return new F(function(){return _2z(_2D,_5);});},_2E=function(_2F,_2G,_2H){return new F(function(){return _2z(_2G,_2H);});},_2I=44,_2J=93,_2K=91,_2L=function(_2M,_2N,_2O){var _2P=E(_2N);if(!_2P._){return new F(function(){return unAppCStr("[]",_2O);});}else{var _2Q=new T(function(){var _2R=new T(function(){var _2S=function(_2T){var _2U=E(_2T);if(!_2U._){return E(new T2(1,_2J,_2O));}else{var _2V=new T(function(){return B(A2(_2M,_2U.a,new T(function(){return B(_2S(_2U.b));})));});return new T2(1,_2I,_2V);}};return B(_2S(_2P.b));});return B(A2(_2M,_2P.a,_2R));});return new T2(1,_2K,_2Q);}},_2W=function(_2X,_2Y){return new F(function(){return _2L(_2z,_2X,_2Y);});},_2Z=new T3(0,_2E,_2C,_2W),_30=new T(function(){return new T5(0,_2e,_2Z,_31,_2q,_2C);}),_31=function(_32){return new T2(0,_30,_32);},_33=3,_34=new T(function(){return B(_31(_33));}),_35=new T(function(){return die(_34);}),_36=function(_37,_38){var _39=E(_37);if(!_39._){var _3a=_39.a,_3b=E(_38);return (_3b._==0)?_3a==_3b.a:(I_compareInt(_3b.a,_3a)==0)?true:false;}else{var _3c=_39.a,_3d=E(_38);return (_3d._==0)?(I_compareInt(_3c,_3d.a)==0)?true:false:(I_compare(_3c,_3d.a)==0)?true:false;}},_3e=new T1(0,0),_3f=function(_3g,_3h){if(!B(_36(_3h,_3e))){return new F(function(){return _21(_3g,_3h);});}else{return E(_35);}},_3i=function(_3j,_3k){var _3l=_3j%_3k;if(_3j<=0){if(_3j>=0){return E(_3l);}else{if(_3k<=0){return E(_3l);}else{var _3m=E(_3l);return (_3m==0)?0:_3m+_3k|0;}}}else{if(_3k>=0){if(_3j>=0){return E(_3l);}else{if(_3k<=0){return E(_3l);}else{var _3n=E(_3l);return (_3n==0)?0:_3n+_3k|0;}}}else{var _3o=E(_3l);return (_3o==0)?0:_3o+_3k|0;}}},_3p=function(_3q,_3r){while(1){var _3s=E(_3q);if(!_3s._){var _3t=E(_3s.a);if(_3t==( -2147483648)){_3q=new T1(1,I_fromInt( -2147483648));continue;}else{var _3u=E(_3r);if(!_3u._){var _3v=_3u.a;return new T2(0,new T1(0,B(_1Y(_3t,_3v))),new T1(0,B(_3i(_3t,_3v))));}else{_3q=new T1(1,I_fromInt(_3t));_3r=_3u;continue;}}}else{var _3w=E(_3r);if(!_3w._){_3q=_3s;_3r=new T1(1,I_fromInt(_3w.a));continue;}else{var _3x=I_divMod(_3s.a,_3w.a);return new T2(0,new T1(1,_3x.a),new T1(1,_3x.b));}}}},_3y=function(_3z,_3A){if(!B(_36(_3A,_3e))){var _3B=B(_3p(_3z,_3A));return new T2(0,_3B.a,_3B.b);}else{return E(_35);}},_3C=function(_3D,_3E){while(1){var _3F=E(_3D);if(!_3F._){var _3G=E(_3F.a);if(_3G==( -2147483648)){_3D=new T1(1,I_fromInt( -2147483648));continue;}else{var _3H=E(_3E);if(!_3H._){return new T1(0,B(_3i(_3G,_3H.a)));}else{_3D=new T1(1,I_fromInt(_3G));_3E=_3H;continue;}}}else{var _3I=_3F.a,_3J=E(_3E);return (_3J._==0)?new T1(1,I_mod(_3I,I_fromInt(_3J.a))):new T1(1,I_mod(_3I,_3J.a));}}},_3K=function(_3L,_3M){if(!B(_36(_3M,_3e))){return new F(function(){return _3C(_3L,_3M);});}else{return E(_35);}},_3N=function(_3O,_3P){while(1){var _3Q=E(_3O);if(!_3Q._){var _3R=E(_3Q.a);if(_3R==( -2147483648)){_3O=new T1(1,I_fromInt( -2147483648));continue;}else{var _3S=E(_3P);if(!_3S._){return new T1(0,quot(_3R,_3S.a));}else{_3O=new T1(1,I_fromInt(_3R));_3P=_3S;continue;}}}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?new T1(0,I_toInt(I_quot(_3T,I_fromInt(_3U.a)))):new T1(1,I_quot(_3T,_3U.a));}}},_3V=function(_3W,_3X){if(!B(_36(_3X,_3e))){return new F(function(){return _3N(_3W,_3X);});}else{return E(_35);}},_3Y=function(_3Z,_40){while(1){var _41=E(_3Z);if(!_41._){var _42=E(_41.a);if(_42==( -2147483648)){_3Z=new T1(1,I_fromInt( -2147483648));continue;}else{var _43=E(_40);if(!_43._){var _44=_43.a;return new T2(0,new T1(0,quot(_42,_44)),new T1(0,_42%_44));}else{_3Z=new T1(1,I_fromInt(_42));_40=_43;continue;}}}else{var _45=E(_40);if(!_45._){_3Z=_41;_40=new T1(1,I_fromInt(_45.a));continue;}else{var _46=I_quotRem(_41.a,_45.a);return new T2(0,new T1(1,_46.a),new T1(1,_46.b));}}}},_47=function(_48,_49){if(!B(_36(_49,_3e))){var _4a=B(_3Y(_48,_49));return new T2(0,_4a.a,_4a.b);}else{return E(_35);}},_4b=function(_4c,_4d){while(1){var _4e=E(_4c);if(!_4e._){var _4f=E(_4e.a);if(_4f==( -2147483648)){_4c=new T1(1,I_fromInt( -2147483648));continue;}else{var _4g=E(_4d);if(!_4g._){return new T1(0,_4f%_4g.a);}else{_4c=new T1(1,I_fromInt(_4f));_4d=_4g;continue;}}}else{var _4h=_4e.a,_4i=E(_4d);return (_4i._==0)?new T1(1,I_rem(_4h,I_fromInt(_4i.a))):new T1(1,I_rem(_4h,_4i.a));}}},_4j=function(_4k,_4l){if(!B(_36(_4l,_3e))){return new F(function(){return _4b(_4k,_4l);});}else{return E(_35);}},_4m=function(_4n){return E(_4n);},_4o=function(_4p){return E(_4p);},_4q=new T1(0,1),_4r=new T1(0,2147483647),_4s=new T(function(){return B(_C(_4r,_4q));}),_4t=function(_4u){var _4v=E(_4u);if(!_4v._){var _4w=E(_4v.a);return (_4w==( -2147483648))?E(_4s):(_4w<0)?new T1(0, -_4w):E(_4v);}else{var _4x=_4v.a;return (I_compareInt(_4x,0)>=0)?E(_4v):new T1(1,I_negate(_4x));}},_4y=function(_4z){var _4A=E(_4z);if(!_4A._){var _4B=E(_4A.a);return (_4B==( -2147483648))?E(_4s):new T1(0, -_4B);}else{return new T1(1,I_negate(_4A.a));}},_4C=new T1(0,0),_4D=new T1(0, -1),_4E=function(_4F){var _4G=E(_4F);if(!_4G._){var _4H=_4G.a;return (_4H>=0)?(E(_4H)==0)?E(_4C):E(_4q):E(_4D);}else{var _4I=I_compareInt(_4G.a,0);return (_4I<=0)?(E(_4I)==0)?E(_4C):E(_4D):E(_4q);}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a;if(!(imul(_4N,_4P)|0)){return new T1(0,imul(_4N,_4P)|0);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4Q=E(_4L);if(!_4Q._){_4K=_4M;_4L=new T1(1,I_fromInt(_4Q.a));continue;}else{return new T1(1,I_mul(_4M.a,_4Q.a));}}}},_4R={_:0,a:_C,b:_T,c:_4J,d:_4y,e:_4t,f:_4E,g:_4o},_4S=function(_4T,_4U){var _4V=E(_4T);if(!_4V._){var _4W=_4V.a,_4X=E(_4U);return (_4X._==0)?_4W!=_4X.a:(I_compareInt(_4X.a,_4W)==0)?false:true;}else{var _4Y=_4V.a,_4Z=E(_4U);return (_4Z._==0)?(I_compareInt(_4Y,_4Z.a)==0)?false:true:(I_compare(_4Y,_4Z.a)==0)?false:true;}},_50=new T2(0,_36,_4S),_51=function(_52,_53){var _54=E(_52);if(!_54._){var _55=_54.a,_56=E(_53);return (_56._==0)?_55<=_56.a:I_compareInt(_56.a,_55)>=0;}else{var _57=_54.a,_58=E(_53);return (_58._==0)?I_compareInt(_57,_58.a)<=0:I_compare(_57,_58.a)<=0;}},_59=function(_5a,_5b){return (!B(_51(_5a,_5b)))?E(_5a):E(_5b);},_5c=function(_5d,_5e){return (!B(_51(_5d,_5e)))?E(_5e):E(_5d);},_5f=function(_5g,_5h){var _5i=E(_5g);if(!_5i._){var _5j=_5i.a,_5k=E(_5h);if(!_5k._){var _5l=_5k.a;return (_5j!=_5l)?(_5j>_5l)?2:0:1;}else{var _5m=I_compareInt(_5k.a,_5j);return (_5m<=0)?(_5m>=0)?1:2:0;}}else{var _5n=_5i.a,_5o=E(_5h);if(!_5o._){var _5p=I_compareInt(_5n,_5o.a);return (_5p>=0)?(_5p<=0)?1:2:0;}else{var _5q=I_compare(_5n,_5o.a);return (_5q>=0)?(_5q<=0)?1:2:0;}}},_5r={_:0,a:_50,b:_5f,c:_1n,d:_51,e:_1f,f:_17,g:_59,h:_5c},_5s=new T1(0,1),_5t=function(_5u){return new T2(0,E(_5u),E(_5s));},_5v=new T3(0,_4R,_5r,_5t),_5w={_:0,a:_5v,b:_1X,c:_3V,d:_4j,e:_3f,f:_3K,g:_47,h:_3y,i:_4m},_5x=function(_5y){while(1){var _5z=E(_5y);if(!_5z._){_5y=new T1(1,I_fromInt(_5z.a));continue;}else{return new F(function(){return I_toString(_5z.a);});}}},_5A=function(_5B,_5C){return new F(function(){return _x(fromJSStr(B(_5x(_5B))),_5C);});},_5D=41,_5E=40,_5F=new T1(0,0),_5G=function(_5H,_5I,_5J){if(_5H<=6){return new F(function(){return _5A(_5I,_5J);});}else{if(!B(_1n(_5I,_5F))){return new F(function(){return _5A(_5I,_5J);});}else{return new T2(1,_5E,new T(function(){return B(_x(fromJSStr(B(_5x(_5I))),new T2(1,_5D,_5J)));}));}}},_5K=function(_5L){return new F(function(){return _5G(0,_5L,_5);});},_5M=function(_5N,_5O){var _5P=E(_5N);if(!_5P._){return new F(function(){return unAppCStr("[]",_5O);});}else{var _5Q=new T(function(){var _5R=new T(function(){var _5S=function(_5T){var _5U=E(_5T);if(!_5U._){return E(new T2(1,_2J,_5O));}else{var _5V=new T(function(){return B(_5G(0,_5U.a,new T(function(){return B(_5S(_5U.b));})));});return new T2(1,_2I,_5V);}};return B(_5S(_5P.b));});return B(_5G(0,_5P.a,_5R));});return new T2(1,_2K,_5Q);}},_5W=function(_5X,_5Y,_5Z){return new F(function(){return _5G(E(_5X),_5Y,_5Z);});},_60=new T3(0,_5W,_5K,_5M),_61=function(_62){var _63=I_decodeDouble(_62);return new T2(0,new T1(1,_63.b),_63.a);},_64=function(_65){var _66=hs_intToInt64(2147483647),_67=hs_leInt64(_65,_66);if(!_67){return new T1(1,I_fromInt64(_65));}else{var _68=hs_intToInt64( -2147483648),_69=hs_geInt64(_65,_68);if(!_69){return new T1(1,I_fromInt64(_65));}else{var _6a=hs_int64ToInt(_65);return new F(function(){return _1T(_6a);});}}},_6b=function(_6c){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_6c>=0){var _6d=jsShowI(_6c);return fromJSStr(_6d);}else{var _6e=jsShowI(_6c);return fromJSStr(_6e);}}))));});},_6f=function(_6g){var _6h=function(_6i){if(_6g<10){return new F(function(){return _6b(_6g);});}else{if(_6g>15){return new F(function(){return _6b(_6g);});}else{return (97+_6g|0)-10|0;}}};if(_6g<0){return new F(function(){return _6h(_);});}else{if(_6g>9){return new F(function(){return _6h(_);});}else{return 48+_6g|0;}}},_6j=function(_6k){return new F(function(){return _6f(E(_6k));});},_6l=function(_6m){var _6n=hs_intToInt64(_6m);return E(_6n);},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){return new F(function(){return _6l(_6q.a);});}else{return new F(function(){return I_toInt64(_6q.a);});}},_6r=new T1(0,255),_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v._){_6t=new T1(1,I_fromInt(_6v.a));continue;}else{return new T1(1,I_shiftLeft(_6v.a,_6u));}}},_6w=new T1(0,16),_6x=function(_6y){return E(E(_6y).a);},_6z=function(_6A){return E(E(_6A).a);},_6B=function(_6C){return E(E(_6C).a);},_6D=function(_6E){return E(E(_6E).b);},_6F=function(_6G){return E(E(_6G).c);},_6H=function(_6I){return E(E(_6I).d);},_6J=function(_6K){return E(E(_6K).a);},_6L=function(_6M){return E(E(_6M).g);},_6N=function(_6O){return E(E(_6O).b);},_6P=function(_6Q,_6R){return new F(function(){return err(B(unAppCStr("Numeric.showIntAtBase: applied to negative number ",new T(function(){return B(A2(_6N,_6R,_6Q));}))));});},_6S=function(_6T,_6U){return new F(function(){return err(B(unAppCStr("Numeric.showIntAtBase: applied to unsupported base ",new T(function(){return B(A2(_6N,_6U,_6T));}))));});},_6V=new T1(0,1),_6W=function(_6X){return E(E(_6X).g);},_6Y=new T1(0,0),_6Z=function(_70){return E(E(_70).i);},_71=function(_72,_73,_74,_75,_76,_77){var _78=B(_6x(_72)),_79=new T(function(){return B(_6B(_78));}),_7a=B(_6D(_78));if(!B(A3(_6H,_7a,_74,new T(function(){return B(A2(_6L,_79,_6V));})))){if(!B(A3(_6F,_7a,_76,new T(function(){return B(A2(_6L,_79,_6Y));})))){var _7b=B(A3(_6W,_72,_76,_74)),_7c=new T(function(){return B(A2(_6L,_79,_6Y));}),_7d=function(_7e,_7f,_7g){while(1){var _7h=B((function(_7i,_7j,_7k){var _7l=B(A1(_75,new T(function(){return B(_1K(B(A2(_6Z,_72,_7j))));})));if(!B(A3(_6J,B(_6z(_7a)),_7i,_7c))){var _7m=B(A3(_6W,_72,_7i,_74)),_7n=new T2(1,_7l,_7k);_7e=_7m.a;_7f=_7m.b;_7g=_7n;return __continue;}else{return new T2(1,_7l,_7k);}})(_7e,_7f,_7g));if(_7h!=__continue){return _7h;}}};return new F(function(){return _7d(_7b.a,_7b.b,_77);});}else{return new F(function(){return _6P(_76,_73);});}}else{return new F(function(){return _6S(_74,_73);});}},_7o=function(_7p){return new F(function(){return _71(_5w,_60,_6w,_6j,new T(function(){var _7q=rintDouble(255*E(_7p)),_7r=B(_61(_7q)),_7s=_7r.a,_7t=_7r.b;if(_7t>=0){var _7u=B(_6s(_7s,_7t));}else{var _7v=hs_uncheckedIShiftRA64(B(_6o(_7s)), -_7t),_7u=B(_64(_7v));}if(!B(_51(_6r,_7u))){return E(_7u);}else{return E(_6r);}}),_5);});},_7w=function(_7x,_7y,_7z){var _7A=new T(function(){var _7B=new T(function(){return B(_x(B(_7o(_7y)),new T(function(){return B(_7o(_7z));},1)));},1);return B(_x(B(_7o(_7x)),_7B));});return new F(function(){return unAppCStr("#",_7A);});},_7C=new T0(1),_7D=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_7E=function(_7F){return new F(function(){return err(_7D);});},_7G=new T(function(){return B(_7E(_));}),_7H=function(_7I,_7J,_7K,_7L){var _7M=E(_7K);if(!_7M._){var _7N=_7M.a,_7O=E(_7L);if(!_7O._){var _7P=_7O.a,_7Q=_7O.b,_7R=_7O.c;if(_7P<=(imul(3,_7N)|0)){return new T5(0,(1+_7N|0)+_7P|0,E(_7I),_7J,E(_7M),E(_7O));}else{var _7S=E(_7O.d);if(!_7S._){var _7T=_7S.a,_7U=_7S.b,_7V=_7S.c,_7W=_7S.d,_7X=E(_7O.e);if(!_7X._){var _7Y=_7X.a;if(_7T>=(imul(2,_7Y)|0)){var _7Z=function(_80){var _81=E(_7I),_82=E(_7S.e);return (_82._==0)?new T5(0,(1+_7N|0)+_7P|0,E(_7U),_7V,E(new T5(0,(1+_7N|0)+_80|0,E(_81),_7J,E(_7M),E(_7W))),E(new T5(0,(1+_7Y|0)+_82.a|0,E(_7Q),_7R,E(_82),E(_7X)))):new T5(0,(1+_7N|0)+_7P|0,E(_7U),_7V,E(new T5(0,(1+_7N|0)+_80|0,E(_81),_7J,E(_7M),E(_7W))),E(new T5(0,1+_7Y|0,E(_7Q),_7R,E(_7C),E(_7X))));},_83=E(_7W);if(!_83._){return new F(function(){return _7Z(_83.a);});}else{return new F(function(){return _7Z(0);});}}else{return new T5(0,(1+_7N|0)+_7P|0,E(_7Q),_7R,E(new T5(0,(1+_7N|0)+_7T|0,E(_7I),_7J,E(_7M),E(_7S))),E(_7X));}}else{return E(_7G);}}else{return E(_7G);}}}else{return new T5(0,1+_7N|0,E(_7I),_7J,E(_7M),E(_7C));}}else{var _84=E(_7L);if(!_84._){var _85=_84.a,_86=_84.b,_87=_84.c,_88=_84.e,_89=E(_84.d);if(!_89._){var _8a=_89.a,_8b=_89.b,_8c=_89.c,_8d=_89.d,_8e=E(_88);if(!_8e._){var _8f=_8e.a;if(_8a>=(imul(2,_8f)|0)){var _8g=function(_8h){var _8i=E(_7I),_8j=E(_89.e);return (_8j._==0)?new T5(0,1+_85|0,E(_8b),_8c,E(new T5(0,1+_8h|0,E(_8i),_7J,E(_7C),E(_8d))),E(new T5(0,(1+_8f|0)+_8j.a|0,E(_86),_87,E(_8j),E(_8e)))):new T5(0,1+_85|0,E(_8b),_8c,E(new T5(0,1+_8h|0,E(_8i),_7J,E(_7C),E(_8d))),E(new T5(0,1+_8f|0,E(_86),_87,E(_7C),E(_8e))));},_8k=E(_8d);if(!_8k._){return new F(function(){return _8g(_8k.a);});}else{return new F(function(){return _8g(0);});}}else{return new T5(0,1+_85|0,E(_86),_87,E(new T5(0,1+_8a|0,E(_7I),_7J,E(_7C),E(_89))),E(_8e));}}else{return new T5(0,3,E(_8b),_8c,E(new T5(0,1,E(_7I),_7J,E(_7C),E(_7C))),E(new T5(0,1,E(_86),_87,E(_7C),E(_7C))));}}else{var _8l=E(_88);return (_8l._==0)?new T5(0,3,E(_86),_87,E(new T5(0,1,E(_7I),_7J,E(_7C),E(_7C))),E(_8l)):new T5(0,2,E(_7I),_7J,E(_7C),E(_84));}}else{return new T5(0,1,E(_7I),_7J,E(_7C),E(_7C));}}},_8m=function(_8n,_8o){return new T5(0,1,E(_8n),_8o,E(_7C),E(_7C));},_8p=function(_8q,_8r,_8s){var _8t=E(_8s);if(!_8t._){return new F(function(){return _7H(_8t.b,_8t.c,_8t.d,B(_8p(_8q,_8r,_8t.e)));});}else{return new F(function(){return _8m(_8q,_8r);});}},_8u=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_8v=function(_8w){return new F(function(){return err(_8u);});},_8x=new T(function(){return B(_8v(_));}),_8y=function(_8z,_8A,_8B,_8C){var _8D=E(_8C);if(!_8D._){var _8E=_8D.a,_8F=E(_8B);if(!_8F._){var _8G=_8F.a,_8H=_8F.b,_8I=_8F.c;if(_8G<=(imul(3,_8E)|0)){return new T5(0,(1+_8G|0)+_8E|0,E(_8z),_8A,E(_8F),E(_8D));}else{var _8J=E(_8F.d);if(!_8J._){var _8K=_8J.a,_8L=E(_8F.e);if(!_8L._){var _8M=_8L.a,_8N=_8L.b,_8O=_8L.c,_8P=_8L.d;if(_8M>=(imul(2,_8K)|0)){var _8Q=function(_8R){var _8S=E(_8L.e);return (_8S._==0)?new T5(0,(1+_8G|0)+_8E|0,E(_8N),_8O,E(new T5(0,(1+_8K|0)+_8R|0,E(_8H),_8I,E(_8J),E(_8P))),E(new T5(0,(1+_8E|0)+_8S.a|0,E(_8z),_8A,E(_8S),E(_8D)))):new T5(0,(1+_8G|0)+_8E|0,E(_8N),_8O,E(new T5(0,(1+_8K|0)+_8R|0,E(_8H),_8I,E(_8J),E(_8P))),E(new T5(0,1+_8E|0,E(_8z),_8A,E(_7C),E(_8D))));},_8T=E(_8P);if(!_8T._){return new F(function(){return _8Q(_8T.a);});}else{return new F(function(){return _8Q(0);});}}else{return new T5(0,(1+_8G|0)+_8E|0,E(_8H),_8I,E(_8J),E(new T5(0,(1+_8E|0)+_8M|0,E(_8z),_8A,E(_8L),E(_8D))));}}else{return E(_8x);}}else{return E(_8x);}}}else{return new T5(0,1+_8E|0,E(_8z),_8A,E(_7C),E(_8D));}}else{var _8U=E(_8B);if(!_8U._){var _8V=_8U.a,_8W=_8U.b,_8X=_8U.c,_8Y=_8U.e,_8Z=E(_8U.d);if(!_8Z._){var _90=_8Z.a,_91=E(_8Y);if(!_91._){var _92=_91.a,_93=_91.b,_94=_91.c,_95=_91.d;if(_92>=(imul(2,_90)|0)){var _96=function(_97){var _98=E(_91.e);return (_98._==0)?new T5(0,1+_8V|0,E(_93),_94,E(new T5(0,(1+_90|0)+_97|0,E(_8W),_8X,E(_8Z),E(_95))),E(new T5(0,1+_98.a|0,E(_8z),_8A,E(_98),E(_7C)))):new T5(0,1+_8V|0,E(_93),_94,E(new T5(0,(1+_90|0)+_97|0,E(_8W),_8X,E(_8Z),E(_95))),E(new T5(0,1,E(_8z),_8A,E(_7C),E(_7C))));},_99=E(_95);if(!_99._){return new F(function(){return _96(_99.a);});}else{return new F(function(){return _96(0);});}}else{return new T5(0,1+_8V|0,E(_8W),_8X,E(_8Z),E(new T5(0,1+_92|0,E(_8z),_8A,E(_91),E(_7C))));}}else{return new T5(0,3,E(_8W),_8X,E(_8Z),E(new T5(0,1,E(_8z),_8A,E(_7C),E(_7C))));}}else{var _9a=E(_8Y);return (_9a._==0)?new T5(0,3,E(_9a.b),_9a.c,E(new T5(0,1,E(_8W),_8X,E(_7C),E(_7C))),E(new T5(0,1,E(_8z),_8A,E(_7C),E(_7C)))):new T5(0,2,E(_8z),_8A,E(_8U),E(_7C));}}else{return new T5(0,1,E(_8z),_8A,E(_7C),E(_7C));}}},_9b=function(_9c,_9d,_9e){var _9f=E(_9e);if(!_9f._){return new F(function(){return _8y(_9f.b,_9f.c,B(_9b(_9c,_9d,_9f.d)),_9f.e);});}else{return new F(function(){return _8m(_9c,_9d);});}},_9g=function(_9h,_9i,_9j,_9k,_9l,_9m,_9n){return new F(function(){return _8y(_9k,_9l,B(_9b(_9h,_9i,_9m)),_9n);});},_9o=function(_9p,_9q,_9r,_9s,_9t,_9u,_9v,_9w){var _9x=E(_9r);if(!_9x._){var _9y=_9x.a,_9z=_9x.b,_9A=_9x.c,_9B=_9x.d,_9C=_9x.e;if((imul(3,_9y)|0)>=_9s){if((imul(3,_9s)|0)>=_9y){return new T5(0,(_9y+_9s|0)+1|0,E(_9p),_9q,E(_9x),E(new T5(0,_9s,E(_9t),_9u,E(_9v),E(_9w))));}else{return new F(function(){return _7H(_9z,_9A,_9B,B(_9o(_9p,_9q,_9C,_9s,_9t,_9u,_9v,_9w)));});}}else{return new F(function(){return _8y(_9t,_9u,B(_9D(_9p,_9q,_9y,_9z,_9A,_9B,_9C,_9v)),_9w);});}}else{return new F(function(){return _9g(_9p,_9q,_9s,_9t,_9u,_9v,_9w);});}},_9D=function(_9E,_9F,_9G,_9H,_9I,_9J,_9K,_9L){var _9M=E(_9L);if(!_9M._){var _9N=_9M.a,_9O=_9M.b,_9P=_9M.c,_9Q=_9M.d,_9R=_9M.e;if((imul(3,_9G)|0)>=_9N){if((imul(3,_9N)|0)>=_9G){return new T5(0,(_9G+_9N|0)+1|0,E(_9E),_9F,E(new T5(0,_9G,E(_9H),_9I,E(_9J),E(_9K))),E(_9M));}else{return new F(function(){return _7H(_9H,_9I,_9J,B(_9o(_9E,_9F,_9K,_9N,_9O,_9P,_9Q,_9R)));});}}else{return new F(function(){return _8y(_9O,_9P,B(_9D(_9E,_9F,_9G,_9H,_9I,_9J,_9K,_9Q)),_9R);});}}else{return new F(function(){return _8p(_9E,_9F,new T5(0,_9G,E(_9H),_9I,E(_9J),E(_9K)));});}},_9S=function(_9T,_9U,_9V,_9W){var _9X=E(_9V);if(!_9X._){var _9Y=_9X.a,_9Z=_9X.b,_a0=_9X.c,_a1=_9X.d,_a2=_9X.e,_a3=E(_9W);if(!_a3._){var _a4=_a3.a,_a5=_a3.b,_a6=_a3.c,_a7=_a3.d,_a8=_a3.e;if((imul(3,_9Y)|0)>=_a4){if((imul(3,_a4)|0)>=_9Y){return new T5(0,(_9Y+_a4|0)+1|0,E(_9T),_9U,E(_9X),E(_a3));}else{return new F(function(){return _7H(_9Z,_a0,_a1,B(_9o(_9T,_9U,_a2,_a4,_a5,_a6,_a7,_a8)));});}}else{return new F(function(){return _8y(_a5,_a6,B(_9D(_9T,_9U,_9Y,_9Z,_a0,_a1,_a2,_a7)),_a8);});}}else{return new F(function(){return _8p(_9T,_9U,_9X);});}}else{return new F(function(){return _9b(_9T,_9U,_9W);});}},_a9=function(_aa,_ab,_ac,_ad,_ae){var _af=E(_aa);if(_af==1){var _ag=E(_ae);if(!_ag._){return new T3(0,new T5(0,1,E(new T2(0,_ab,_ac)),_ad,E(_7C),E(_7C)),_5,_5);}else{var _ah=E(E(_ag.a).a),_ai=E(_ah.a);return (_ab>=_ai)?(_ab!=_ai)?new T3(0,new T5(0,1,E(new T2(0,_ab,_ac)),_ad,E(_7C),E(_7C)),_5,_ag):(_ac<E(_ah.b))?new T3(0,new T5(0,1,E(new T2(0,_ab,_ac)),_ad,E(_7C),E(_7C)),_ag,_5):new T3(0,new T5(0,1,E(new T2(0,_ab,_ac)),_ad,E(_7C),E(_7C)),_5,_ag):new T3(0,new T5(0,1,E(new T2(0,_ab,_ac)),_ad,E(_7C),E(_7C)),_ag,_5);}}else{var _aj=B(_a9(_af>>1,_ab,_ac,_ad,_ae)),_ak=_aj.a,_al=_aj.c,_am=E(_aj.b);if(!_am._){return new T3(0,_ak,_5,_al);}else{var _an=E(_am.a),_ao=_an.a,_ap=_an.b,_aq=E(_am.b);if(!_aq._){return new T3(0,new T(function(){return B(_8p(_ao,_ap,_ak));}),_5,_al);}else{var _ar=_aq.b,_as=E(_aq.a),_at=_as.b,_au=E(_ao),_av=E(_as.a),_aw=_av.b,_ax=E(_au.a),_ay=E(_av.a);if(_ax>=_ay){if(_ax!=_ay){return new T3(0,_ak,_5,_am);}else{var _az=E(_aw);if(E(_au.b)<_az){var _aA=B(_a9(_af>>1,_ay,_az,_at,_ar));return new T3(0,new T(function(){return B(_9S(_au,_ap,_ak,_aA.a));}),_aA.b,_aA.c);}else{return new T3(0,_ak,_5,_am);}}}else{var _aB=B(_aC(_af>>1,_ay,_aw,_at,_ar));return new T3(0,new T(function(){return B(_9S(_au,_ap,_ak,_aB.a));}),_aB.b,_aB.c);}}}}},_aC=function(_aD,_aE,_aF,_aG,_aH){var _aI=E(_aD);if(_aI==1){var _aJ=E(_aH);if(!_aJ._){return new T3(0,new T5(0,1,E(new T2(0,_aE,_aF)),_aG,E(_7C),E(_7C)),_5,_5);}else{var _aK=E(E(_aJ.a).a),_aL=E(_aK.a);if(_aE>=_aL){if(_aE!=_aL){return new T3(0,new T5(0,1,E(new T2(0,_aE,_aF)),_aG,E(_7C),E(_7C)),_5,_aJ);}else{var _aM=E(_aF);return (_aM<E(_aK.b))?new T3(0,new T5(0,1,E(new T2(0,_aE,_aM)),_aG,E(_7C),E(_7C)),_aJ,_5):new T3(0,new T5(0,1,E(new T2(0,_aE,_aM)),_aG,E(_7C),E(_7C)),_5,_aJ);}}else{return new T3(0,new T5(0,1,E(new T2(0,_aE,_aF)),_aG,E(_7C),E(_7C)),_aJ,_5);}}}else{var _aN=B(_aC(_aI>>1,_aE,_aF,_aG,_aH)),_aO=_aN.a,_aP=_aN.c,_aQ=E(_aN.b);if(!_aQ._){return new T3(0,_aO,_5,_aP);}else{var _aR=E(_aQ.a),_aS=_aR.a,_aT=_aR.b,_aU=E(_aQ.b);if(!_aU._){return new T3(0,new T(function(){return B(_8p(_aS,_aT,_aO));}),_5,_aP);}else{var _aV=_aU.b,_aW=E(_aU.a),_aX=_aW.b,_aY=E(_aS),_aZ=E(_aW.a),_b0=_aZ.b,_b1=E(_aY.a),_b2=E(_aZ.a);if(_b1>=_b2){if(_b1!=_b2){return new T3(0,_aO,_5,_aQ);}else{var _b3=E(_b0);if(E(_aY.b)<_b3){var _b4=B(_a9(_aI>>1,_b2,_b3,_aX,_aV));return new T3(0,new T(function(){return B(_9S(_aY,_aT,_aO,_b4.a));}),_b4.b,_b4.c);}else{return new T3(0,_aO,_5,_aQ);}}}else{var _b5=B(_aC(_aI>>1,_b2,_b0,_aX,_aV));return new T3(0,new T(function(){return B(_9S(_aY,_aT,_aO,_b5.a));}),_b5.b,_b5.c);}}}}},_b6=function(_b7,_b8,_b9,_ba){var _bb=E(_ba);if(!_bb._){var _bc=_bb.c,_bd=_bb.d,_be=_bb.e,_bf=E(_bb.b),_bg=E(_bf.a);if(_b7>=_bg){if(_b7!=_bg){return new F(function(){return _7H(_bf,_bc,_bd,B(_b6(_b7,_b8,_b9,_be)));});}else{var _bh=E(_bf.b);if(_b8>=_bh){if(_b8!=_bh){return new F(function(){return _7H(_bf,_bc,_bd,B(_b6(_b7,_b8,_b9,_be)));});}else{return new T5(0,_bb.a,E(new T2(0,_b7,_b8)),_b9,E(_bd),E(_be));}}else{return new F(function(){return _8y(_bf,_bc,B(_b6(_b7,_b8,_b9,_bd)),_be);});}}}else{return new F(function(){return _8y(_bf,_bc,B(_b6(_b7,_b8,_b9,_bd)),_be);});}}else{return new T5(0,1,E(new T2(0,_b7,_b8)),_b9,E(_7C),E(_7C));}},_bi=function(_bj,_bk,_bl,_bm){var _bn=E(_bm);if(!_bn._){var _bo=_bn.c,_bp=_bn.d,_bq=_bn.e,_br=E(_bn.b),_bs=E(_br.a);if(_bj>=_bs){if(_bj!=_bs){return new F(function(){return _7H(_br,_bo,_bp,B(_bi(_bj,_bk,_bl,_bq)));});}else{var _bt=E(_bk),_bu=E(_br.b);if(_bt>=_bu){if(_bt!=_bu){return new F(function(){return _7H(_br,_bo,_bp,B(_b6(_bj,_bt,_bl,_bq)));});}else{return new T5(0,_bn.a,E(new T2(0,_bj,_bt)),_bl,E(_bp),E(_bq));}}else{return new F(function(){return _8y(_br,_bo,B(_b6(_bj,_bt,_bl,_bp)),_bq);});}}}else{return new F(function(){return _8y(_br,_bo,B(_bi(_bj,_bk,_bl,_bp)),_bq);});}}else{return new T5(0,1,E(new T2(0,_bj,_bk)),_bl,E(_7C),E(_7C));}},_bv=function(_bw,_bx,_by,_bz){var _bA=E(_bz);if(!_bA._){var _bB=_bA.c,_bC=_bA.d,_bD=_bA.e,_bE=E(_bA.b),_bF=E(_bw),_bG=E(_bE.a);if(_bF>=_bG){if(_bF!=_bG){return new F(function(){return _7H(_bE,_bB,_bC,B(_bi(_bF,_bx,_by,_bD)));});}else{var _bH=E(_bx),_bI=E(_bE.b);if(_bH>=_bI){if(_bH!=_bI){return new F(function(){return _7H(_bE,_bB,_bC,B(_b6(_bF,_bH,_by,_bD)));});}else{return new T5(0,_bA.a,E(new T2(0,_bF,_bH)),_by,E(_bC),E(_bD));}}else{return new F(function(){return _8y(_bE,_bB,B(_b6(_bF,_bH,_by,_bC)),_bD);});}}}else{return new F(function(){return _8y(_bE,_bB,B(_bi(_bF,_bx,_by,_bC)),_bD);});}}else{return new T5(0,1,E(new T2(0,_bw,_bx)),_by,E(_7C),E(_7C));}},_bJ=function(_bK,_bL){while(1){var _bM=E(_bL);if(!_bM._){return E(_bK);}else{var _bN=E(_bM.a),_bO=E(_bN.a),_bP=B(_bv(_bO.a,_bO.b,_bN.b,_bK));_bK=_bP;_bL=_bM.b;continue;}}},_bQ=function(_bR,_bS,_bT,_bU,_bV){return new F(function(){return _bJ(B(_bv(_bS,_bT,_bU,_bR)),_bV);});},_bW=function(_bX,_bY,_bZ){var _c0=E(_bY),_c1=E(_c0.a);return new F(function(){return _bJ(B(_bv(_c1.a,_c1.b,_c0.b,_bX)),_bZ);});},_c2=function(_c3,_c4,_c5){var _c6=E(_c5);if(!_c6._){return E(_c4);}else{var _c7=E(_c6.a),_c8=_c7.a,_c9=_c7.b,_ca=E(_c6.b);if(!_ca._){return new F(function(){return _8p(_c8,_c9,_c4);});}else{var _cb=E(_ca.a),_cc=E(_c8),_cd=_cc.b,_ce=E(_cb.a),_cf=_ce.b,_cg=E(_cc.a),_ch=E(_ce.a),_ci=function(_cj){var _ck=B(_aC(_c3,_ch,_cf,_cb.b,_ca.b)),_cl=_ck.a,_cm=E(_ck.c);if(!_cm._){return new F(function(){return _c2(_c3<<1,B(_9S(_cc,_c9,_c4,_cl)),_ck.b);});}else{return new F(function(){return _bW(B(_9S(_cc,_c9,_c4,_cl)),_cm.a,_cm.b);});}};if(_cg>=_ch){if(_cg!=_ch){return new F(function(){return _bQ(_c4,_cg,_cd,_c9,_ca);});}else{var _cn=E(_cd);if(_cn<E(_cf)){return new F(function(){return _ci(_);});}else{return new F(function(){return _bQ(_c4,_cg,_cn,_c9,_ca);});}}}else{return new F(function(){return _ci(_);});}}}},_co=function(_cp,_cq,_cr,_cs,_ct,_cu){var _cv=E(_cu);if(!_cv._){return new F(function(){return _8p(new T2(0,_cr,_cs),_ct,_cq);});}else{var _cw=E(_cv.a),_cx=E(_cw.a),_cy=_cx.b,_cz=E(_cx.a),_cA=function(_cB){var _cC=B(_aC(_cp,_cz,_cy,_cw.b,_cv.b)),_cD=_cC.a,_cE=E(_cC.c);if(!_cE._){return new F(function(){return _c2(_cp<<1,B(_9S(new T2(0,_cr,_cs),_ct,_cq,_cD)),_cC.b);});}else{return new F(function(){return _bW(B(_9S(new T2(0,_cr,_cs),_ct,_cq,_cD)),_cE.a,_cE.b);});}};if(_cr>=_cz){if(_cr!=_cz){return new F(function(){return _bQ(_cq,_cr,_cs,_ct,_cv);});}else{if(_cs<E(_cy)){return new F(function(){return _cA(_);});}else{return new F(function(){return _bQ(_cq,_cr,_cs,_ct,_cv);});}}}else{return new F(function(){return _cA(_);});}}},_cF=function(_cG,_cH,_cI,_cJ,_cK,_cL){var _cM=E(_cL);if(!_cM._){return new F(function(){return _8p(new T2(0,_cI,_cJ),_cK,_cH);});}else{var _cN=E(_cM.a),_cO=E(_cN.a),_cP=_cO.b,_cQ=E(_cO.a),_cR=function(_cS){var _cT=B(_aC(_cG,_cQ,_cP,_cN.b,_cM.b)),_cU=_cT.a,_cV=E(_cT.c);if(!_cV._){return new F(function(){return _c2(_cG<<1,B(_9S(new T2(0,_cI,_cJ),_cK,_cH,_cU)),_cT.b);});}else{return new F(function(){return _bW(B(_9S(new T2(0,_cI,_cJ),_cK,_cH,_cU)),_cV.a,_cV.b);});}};if(_cI>=_cQ){if(_cI!=_cQ){return new F(function(){return _bQ(_cH,_cI,_cJ,_cK,_cM);});}else{var _cW=E(_cJ);if(_cW<E(_cP)){return new F(function(){return _cR(_);});}else{return new F(function(){return _bQ(_cH,_cI,_cW,_cK,_cM);});}}}else{return new F(function(){return _cR(_);});}}},_cX=function(_cY){var _cZ=E(_cY);if(!_cZ._){return new T0(1);}else{var _d0=E(_cZ.a),_d1=_d0.a,_d2=_d0.b,_d3=E(_cZ.b);if(!_d3._){return new T5(0,1,E(_d1),_d2,E(_7C),E(_7C));}else{var _d4=_d3.b,_d5=E(_d3.a),_d6=_d5.b,_d7=E(_d1),_d8=E(_d5.a),_d9=_d8.b,_da=E(_d7.a),_db=E(_d8.a);if(_da>=_db){if(_da!=_db){return new F(function(){return _bQ(new T5(0,1,E(_d7),_d2,E(_7C),E(_7C)),_db,_d9,_d6,_d4);});}else{var _dc=E(_d9);if(E(_d7.b)<_dc){return new F(function(){return _co(1,new T5(0,1,E(_d7),_d2,E(_7C),E(_7C)),_db,_dc,_d6,_d4);});}else{return new F(function(){return _bQ(new T5(0,1,E(_d7),_d2,E(_7C),E(_7C)),_db,_dc,_d6,_d4);});}}}else{return new F(function(){return _cF(1,new T5(0,1,E(_d7),_d2,E(_7C),E(_7C)),_db,_d9,_d6,_d4);});}}}},_dd=new T(function(){return B(unCStr("!!: negative index"));}),_de=new T(function(){return B(unCStr("Prelude."));}),_df=new T(function(){return B(_x(_de,_dd));}),_dg=new T(function(){return B(err(_df));}),_dh=new T(function(){return B(unCStr("!!: index too large"));}),_di=new T(function(){return B(_x(_de,_dh));}),_dj=new T(function(){return B(err(_di));}),_dk=function(_dl,_dm){while(1){var _dn=E(_dl);if(!_dn._){return E(_dj);}else{var _do=E(_dm);if(!_do){return E(_dn.a);}else{_dl=_dn.b;_dm=_do-1|0;continue;}}}},_dp=function(_dq,_dr){if(_dr>=0){return new F(function(){return _dk(_dq,_dr);});}else{return E(_dg);}},_ds=6,_dt=new T2(1,_ds,_5),_du= -1,_dv=new T2(1,_du,_dt),_dw=new T2(1,_du,_dv),_dx=new T2(1,_du,_dw),_dy=14,_dz=new T2(1,_dy,_dx),_dA=7,_dB=new T2(1,_dA,_5),_dC=new T2(1,_du,_dB),_dD=new T2(1,_du,_dC),_dE=new T2(1,_du,_dD),_dF=13,_dG=new T2(1,_dF,_dE),_dH=12,_dI=11,_dJ=10,_dK=9,_dL=8,_dM=new T2(1,_dL,_5),_dN=new T2(1,_dK,_dM),_dO=new T2(1,_dJ,_dN),_dP=new T2(1,_dI,_dO),_dQ=new T2(1,_dH,_dP),_dR=new T2(1,_dQ,_5),_dS=new T2(1,_dG,_dR),_dT=new T2(1,_dz,_dS),_dU=5,_dV=new T2(1,_dU,_5),_dW=new T2(1,_du,_dV),_dX=new T2(1,_du,_dW),_dY=new T2(1,_du,_dX),_dZ=15,_e0=new T2(1,_dZ,_dY),_e1=new T2(1,_e0,_dT),_e2=4,_e3=new T2(1,_e2,_5),_e4=3,_e5=new T2(1,_e4,_e3),_e6=2,_e7=new T2(1,_e6,_e5),_e8=1,_e9=new T2(1,_e8,_e7),_ea=0,_eb=new T2(1,_ea,_e9),_ec=function(_ed,_ee){if(_ed<=_ee){var _ef=function(_eg){return new T2(1,_eg,new T(function(){if(_eg!=_ee){return B(_ef(_eg+1|0));}else{return __Z;}}));};return new F(function(){return _ef(_ed);});}else{return __Z;}},_eh=new T(function(){return B(_ec(0,2147483647));}),_ei=function(_ej,_ek,_el){var _em=E(_ek);if(!_em._){return __Z;}else{var _en=E(_el);return (_en._==0)?__Z:new T2(1,new T(function(){return B(A2(_ej,_em.a,_en.a));}),new T(function(){return B(_ei(_ej,_em.b,_en.b));}));}},_eo=function(_ep){var _eq=function(_er,_es){var _et=E(_er);if(!_et._){return __Z;}else{var _eu=E(_es);if(!_eu._){return __Z;}else{var _ev=function(_ew,_ex){return new T2(0,new T2(0,_ew,_et.a),new T(function(){var _ey=E(_ex);if(_ey==( -1)){return true;}else{return B(_dp(_ep,_ey));}}));};return new F(function(){return _x(B(_ei(_ev,_eh,_eu.a)),new T(function(){return B(_eq(_et.b,_eu.b));},1));});}}},_ez=function(_eA,_eB,_eC){var _eD=E(_eA);if(!_eD._){return __Z;}else{var _eE=function(_eF,_eG){return new T2(0,new T2(0,_eF,_eD.a),new T(function(){var _eH=E(_eG);if(_eH==( -1)){return true;}else{return B(_dp(_ep,_eH));}}));};return new F(function(){return _x(B(_ei(_eE,_eh,_eB)),new T(function(){return B(_eq(_eD.b,_eC));},1));});}};return new F(function(){return _cX(B(_ez(_eh,_eb,_e1)));});},_eI=function(_eJ){var _eK=E(_eJ);if(!_eK._){return new T3(0,_5,_5,_5);}else{var _eL=E(_eK.a),_eM=B(_eI(_eK.b));return new T3(0,new T(function(){return B(_x(_eL.a,_eM.a));}),new T(function(){return B(_x(_eL.b,_eM.b));}),new T(function(){return B(_x(_eL.c,_eM.c));}));}},_eN=10,_eO=function(_eP,_eQ,_eR,_eS,_eT){var _eU=new T(function(){if(!E(_eT)){if(!E(_eS)){return E(_eP)*200;}else{return E(_eP)*200+18;}}else{return E(_eP)*200+18;}}),_eV=new T(function(){if(!E(_eT)){if(!E(_eR)){return E(_eQ)*200;}else{return E(_eQ)*200+18;}}else{return E(_eQ)*200+18;}});return new T3(0,new T(function(){if(!E(_eR)){return E(_eU);}else{if(!E(_eS)){return E(_eU)-18;}else{return E(_eU);}}}),new T(function(){if(!E(_eS)){return E(_eV);}else{if(!E(_eR)){return E(_eV)-18;}else{return E(_eV);}}}),_eN);},_eW=function(_eX){var _eY=E(_eX),_eZ=E(_eY.a),_f0=E(_eY.b),_f1=E(_f0.b),_f2=B(_eO(_eZ.a,_eZ.b,_f1.a,_f1.c,E(_f0.c).a));return new T3(0,_f2.a,_f2.b,_f2.c);},_f3=function(_f4,_f5,_f6,_f7,_f8){var _f9=new T(function(){if(!E(_f8)){if(!E(_f7)){return E(_f4)*200+200;}else{return E(_f4)*200+200-18;}}else{return E(_f4)*200+200-18;}}),_fa=new T(function(){if(!E(_f8)){if(!E(_f6)){return E(_f5)*200+200;}else{return E(_f5)*200+200-18;}}else{return E(_f5)*200+200-18;}});return new T3(0,new T(function(){if(!E(_f6)){return E(_f9);}else{if(!E(_f7)){return E(_f9)+18;}else{return E(_f9);}}}),new T(function(){if(!E(_f7)){return E(_fa);}else{if(!E(_f6)){return E(_fa)+18;}else{return E(_fa);}}}),_eN);},_fb=function(_fc){var _fd=E(_fc),_fe=E(_fd.a),_ff=E(_fd.b),_fg=E(_ff.b),_fh=B(_f3(_fe.a,_fe.b,_fg.b,_fg.d,E(_ff.c).c));return new T3(0,_fh.a,_fh.b,_fh.c);},_fi=function(_fj,_fk,_fl,_fm,_fn){var _fo=new T(function(){if(!E(_fn)){if(!E(_fm)){return E(_fj)*200;}else{return E(_fj)*200+18;}}else{return E(_fj)*200+18;}}),_fp=new T(function(){if(!E(_fn)){if(!E(_fl)){return E(_fk)*200+200;}else{return E(_fk)*200+200-18;}}else{return E(_fk)*200+200-18;}});return new T3(0,new T(function(){if(!E(_fl)){return E(_fo);}else{if(!E(_fm)){return E(_fo)-18;}else{return E(_fo);}}}),new T(function(){if(!E(_fm)){return E(_fp);}else{if(!E(_fl)){return E(_fp)+18;}else{return E(_fp);}}}),_eN);},_fq=function(_fr){var _fs=E(_fr),_ft=E(_fs.a),_fu=E(_fs.b),_fv=E(_fu.b),_fw=B(_fi(_ft.a,_ft.b,_fv.b,_fv.c,E(_fu.c).d));return new T3(0,_fw.a,_fw.b,_fw.c);},_fx=function(_fy){var _fz=E(_fy),_fA=E(_fz.a),_fB=E(_fz.b),_fC=E(_fB.b),_fD=B(_f3(_fA.a,_fA.b,_fC.b,_fC.d,E(_fB.c).c));return new T3(0,_fD.a,_fD.b,new T(function(){return E(_fD.c)+160;}));},_fE=new T2(1,_fx,_5),_fF=function(_fG){var _fH=E(_fG),_fI=E(_fH.a),_fJ=E(_fH.b),_fK=E(_fJ.b),_fL=B(_fi(_fI.a,_fI.b,_fK.b,_fK.c,E(_fJ.c).d));return new T3(0,_fL.a,_fL.b,new T(function(){return E(_fL.c)+160;}));},_fM=new T2(1,_fF,_fE),_fN=new T2(1,_fq,_fM),_fO=new T2(1,_fq,_5),_fP=new T2(1,_fF,_fO),_fQ=function(_fR){var _fS=E(_fR),_fT=E(_fS.a),_fU=E(_fS.b),_fV=E(_fU.b),_fW=B(_eO(_fT.a,_fT.b,_fV.a,_fV.c,E(_fU.c).a));return new T3(0,_fW.a,_fW.b,new T(function(){return E(_fW.c)+160;}));},_fX=new T2(1,_fQ,_fP),_fY=function(_fZ,_g0,_g1,_g2,_g3){var _g4=new T(function(){if(!E(_g3)){if(!E(_g2)){return E(_fZ)*200+200;}else{return E(_fZ)*200+200-18;}}else{return E(_fZ)*200+200-18;}}),_g5=new T(function(){if(!E(_g3)){if(!E(_g1)){return E(_g0)*200;}else{return E(_g0)*200+18;}}else{return E(_g0)*200+18;}});return new T3(0,new T(function(){if(!E(_g1)){return E(_g4);}else{if(!E(_g2)){return E(_g4)+18;}else{return E(_g4);}}}),new T(function(){if(!E(_g2)){return E(_g5);}else{if(!E(_g1)){return E(_g5)-18;}else{return E(_g5);}}}),_eN);},_g6=function(_g7){var _g8=E(_g7),_g9=E(_g8.a),_ga=E(_g8.b),_gb=E(_ga.b),_gc=B(_fY(_g9.a,_g9.b,_gb.a,_gb.d,E(_ga.c).b));return new T3(0,_gc.a,_gc.b,_gc.c);},_gd=new T2(1,_fQ,_5),_ge=function(_gf){var _gg=E(_gf),_gh=E(_gg.a),_gi=E(_gg.b),_gj=E(_gi.b),_gk=B(_fY(_gh.a,_gh.b,_gj.a,_gj.d,E(_gi.c).b));return new T3(0,_gk.a,_gk.b,new T(function(){return E(_gk.c)+160;}));},_gl=new T2(1,_ge,_gd),_gm=new T2(1,_g6,_gl),_gn=new T2(1,_fF,_5),_go=new T2(1,_fx,_gn),_gp=new T2(1,_ge,_go),_gq=new T2(1,_fQ,_gp),_gr=new T2(1,_g6,_5),_gs=new T2(1,_fb,_gr),_gt=new T2(1,_fq,_gs),_gu=new T2(1,_eW,_gt),_gv=new T2(1,_ge,_5),_gw=new T2(1,_fx,_gv),_gx=new T2(1,_fb,_gw),_gy=new T2(1,_g6,_gx),_gz=function(_gA,_gB){while(1){var _gC=B((function(_gD,_gE){var _gF=E(_gE);if(!_gF._){var _gG=new T(function(){var _gH=E(_gF.c),_gI=_gH.a,_gJ=E(_gH.b),_gK=_gJ.d,_gL=new T2(0,_gF.b,_gH),_gM=new T(function(){var _gN=new T(function(){var _gO=new T(function(){var _gP=function(_gQ){return new F(function(){return A1(_gQ,_gL);});};if(!E(_gJ.c)){if(!E(_gK)){return __Z;}else{return B(_6(_gP,_gy));}}else{var _gR=new T(function(){if(!E(_gK)){return __Z;}else{return B(_6(_gP,_gy));}}),_gS=function(_gT){var _gU=E(_gT);return (_gU._==0)?E(_gR):new T2(1,new T(function(){return B(A1(_gU.a,_gL));}),new T(function(){return B(_gS(_gU.b));}));},_gV=function(_gW,_gX){return new T2(1,new T(function(){return B(A1(_gW,_gL));}),new T(function(){return B(_gS(_gX));}));};return B(_gV(_eW,_fX));}});if(!E(_gJ.b)){return E(_gO);}else{var _gY=function(_gZ){var _h0=E(_gZ);return (_h0._==0)?E(_gO):new T2(1,new T(function(){return B(A1(_h0.a,_gL));}),new T(function(){return B(_gY(_h0.b));}));},_h1=function(_h2,_h3){return new T2(1,new T(function(){return B(A1(_h2,_gL));}),new T(function(){return B(_gY(_h3));}));};return B(_h1(_fb,_fN));}});if(!E(_gJ.a)){return E(_gN);}else{var _h4=function(_h5){var _h6=E(_h5);return (_h6._==0)?E(_gN):new T2(1,new T(function(){return B(A1(_h6.a,_gL));}),new T(function(){return B(_h4(_h6.b));}));},_h7=function(_h8,_h9){return new T2(1,new T(function(){return B(A1(_h8,_gL));}),new T(function(){return B(_h4(_h9));}));};return B(_h7(_eW,_gm));}}),_ha=new T(function(){if(!E(_gI)){return __Z;}else{return B(_6(function(_hb){return new F(function(){return A1(_hb,_gL);});},_gu));}}),_hc=new T(function(){if(!E(_gI)){return __Z;}else{return B(_6(function(_hd){return new F(function(){return A1(_hd,_gL);});},_gq));}});return new T3(0,_hc,_ha,_gM);});_gA=new T2(1,_gG,new T(function(){return B(_gz(_gD,_gF.e));}));_gB=_gF.d;return __continue;}else{return E(_gD);}})(_gA,_gB));if(_gC!=__continue){return _gC;}}},_he=function(_hf,_hg,_hh,_hi){while(1){var _hj=E(_hi);if(!_hj._){var _hk=_hj.d,_hl=_hj.e,_hm=E(_hj.b),_hn=E(_hm.a);if(_hg>=_hn){if(_hg!=_hn){_hi=_hl;continue;}else{var _ho=E(_hm.b);if(_hh>=_ho){if(_hh!=_ho){_hi=_hl;continue;}else{return E(_hj.c);}}else{_hi=_hk;continue;}}}else{_hi=_hk;continue;}}else{return E(_hf);}}},_hp=function(_hq,_hr,_hs,_ht){while(1){var _hu=E(_ht);if(!_hu._){var _hv=_hu.d,_hw=_hu.e,_hx=E(_hu.b),_hy=E(_hx.a);if(_hr>=_hy){if(_hr!=_hy){_ht=_hw;continue;}else{var _hz=E(_hs),_hA=E(_hx.b);if(_hz>=_hA){if(_hz!=_hA){return new F(function(){return _he(_hq,_hr,_hz,_hw);});}else{return E(_hu.c);}}else{return new F(function(){return _he(_hq,_hr,_hz,_hv);});}}}else{_ht=_hv;continue;}}else{return E(_hq);}}},_hB=function(_hC,_hD,_hE,_hF){var _hG=E(_hF);if(!_hG._){var _hH=_hG.d,_hI=_hG.e,_hJ=E(_hG.b),_hK=E(_hD),_hL=E(_hJ.a);if(_hK>=_hL){if(_hK!=_hL){return new F(function(){return _hp(_hC,_hK,_hE,_hI);});}else{var _hM=E(_hE),_hN=E(_hJ.b);if(_hM>=_hN){if(_hM!=_hN){return new F(function(){return _he(_hC,_hK,_hM,_hI);});}else{return E(_hG.c);}}else{return new F(function(){return _he(_hC,_hK,_hM,_hH);});}}}else{return new F(function(){return _hp(_hC,_hK,_hE,_hH);});}}else{return E(_hC);}},_hO=false,_hP=function(_hQ){var _hR=function(_hS,_hT){while(1){var _hU=B((function(_hV,_hW){var _hX=E(_hW);if(!_hX._){var _hY=_hX.c,_hZ=E(_hX.b),_i0=_hZ.a,_i1=_hZ.b,_i2=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)-1|0;}),new T(function(){return E(_i1)+1|0;}),_hQ))){return true;}else{return false;}}}),_i3=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)+1|0;}),new T(function(){return E(_i1)+1|0;}),_hQ))){return true;}else{return false;}}}),_i4=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)+1|0;}),new T(function(){return E(_i1)-1|0;}),_hQ))){return true;}else{return false;}}}),_i5=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)-1|0;}),new T(function(){return E(_i1)-1|0;}),_hQ))){return true;}else{return false;}}}),_i6=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)+1|0;}),_i1,_hQ))){return true;}else{return false;}}}),_i7=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,new T(function(){return E(_i0)-1|0;}),_i1,_hQ))){return true;}else{return false;}}}),_i8=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,_i0,new T(function(){return E(_i1)+1|0;}),_hQ))){return true;}else{return false;}}}),_i9=new T(function(){if(!E(_hY)){return false;}else{if(!B(_hB(_hO,_i0,new T(function(){return E(_i1)-1|0;}),_hQ))){return true;}else{return false;}}});_hS=new T2(1,new T2(0,_hZ,new T3(0,_hY,new T4(0,_i9,_i8,_i7,_i6),new T4(0,_i5,_i4,_i3,_i2))),new T(function(){return B(_hR(_hV,_hX.e));}));_hT=_hX.d;return __continue;}else{return E(_hV);}})(_hS,_hT));if(_hU!=__continue){return _hU;}}};return new F(function(){return _cX(B(_hR(_5,_hQ)));});},_ia=function(_ib){return new F(function(){return _eI(B(_gz(_5,B(_hP(B(_eo(_ib)))))));});},_ic=0,_id=new T(function(){return eval("addMeshFromQuads");}),_ie=0.44,_if=new T(function(){return B(unCStr("base"));}),_ig=new T(function(){return B(unCStr("Control.Exception.Base"));}),_ih=new T(function(){return B(unCStr("PatternMatchFail"));}),_ii=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_if,_ig,_ih),_ij=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_ii,_5,_5),_ik=function(_il){return E(_ij);},_im=function(_in){var _io=E(_in);return new F(function(){return _2i(B(_2g(_io.a)),_ik,_io.b);});},_ip=function(_iq){return E(E(_iq).a);},_ir=function(_is){return new T2(0,_it,_is);},_iu=function(_iv,_iw){return new F(function(){return _x(E(_iv).a,_iw);});},_ix=function(_iy,_iz){return new F(function(){return _2L(_iu,_iy,_iz);});},_iA=function(_iB,_iC,_iD){return new F(function(){return _x(E(_iC).a,_iD);});},_iE=new T3(0,_iA,_ip,_ix),_it=new T(function(){return new T5(0,_ik,_iE,_ir,_im,_ip);}),_iF=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_iG=function(_iH){return E(E(_iH).c);},_iI=function(_iJ,_iK){return new F(function(){return die(new T(function(){return B(A2(_iG,_iK,_iJ));}));});},_iL=function(_iM,_32){return new F(function(){return _iI(_iM,_32);});},_iN=function(_iO,_iP){var _iQ=E(_iP);if(!_iQ._){return new T2(0,_5,_5);}else{var _iR=_iQ.a;if(!B(A1(_iO,_iR))){return new T2(0,_5,_iQ);}else{var _iS=new T(function(){var _iT=B(_iN(_iO,_iQ.b));return new T2(0,_iT.a,_iT.b);});return new T2(0,new T2(1,_iR,new T(function(){return E(E(_iS).a);})),new T(function(){return E(E(_iS).b);}));}}},_iU=32,_iV=new T(function(){return B(unCStr("\n"));}),_iW=function(_iX){return (E(_iX)==124)?false:true;},_iY=function(_iZ,_j0){var _j1=B(_iN(_iW,B(unCStr(_iZ)))),_j2=_j1.a,_j3=function(_j4,_j5){var _j6=new T(function(){var _j7=new T(function(){return B(_x(_j0,new T(function(){return B(_x(_j5,_iV));},1)));});return B(unAppCStr(": ",_j7));},1);return new F(function(){return _x(_j4,_j6);});},_j8=E(_j1.b);if(!_j8._){return new F(function(){return _j3(_j2,_5);});}else{if(E(_j8.a)==124){return new F(function(){return _j3(_j2,new T2(1,_iU,_j8.b));});}else{return new F(function(){return _j3(_j2,_5);});}}},_j9=function(_ja){return new F(function(){return _iL(new T1(0,new T(function(){return B(_iY(_ja,_iF));})),_it);});},_jb=new T(function(){return B(_j9("Cube.hs:(119,1)-(124,51)|function lineColor"));}),_jc=0.1,_jd=0.6,_je=0.5,_jf=0.4,_jg=1,_jh=0.22,_ji=0.2,_jj=0.8,_jk=function(_jl,_jm,_){var _jn=E(_jl);if(!_jn._){return _ic;}else{var _jo=E(_jm);if(!_jo._){return _ic;}else{var _jp=E(_jn.a),_jq=function(_jr,_js,_jt){var _ju=E(_id),_jv=__app2(_ju,B(_q(_4,_4,_4,B(_6(_jo.a,B(_ia(_jp.b)).a)))),toJSStr(B(_7w(_jr,_js,_jt)))),_jw=function(_jx,_jy,_){var _jz=E(_jx);if(!_jz._){return _ic;}else{var _jA=E(_jy);if(!_jA._){return _ic;}else{var _jB=E(_jz.a),_jC=function(_jD,_jE,_jF){var _jG=__app2(_ju,B(_q(_4,_4,_4,B(_6(_jA.a,B(_ia(_jB.b)).a)))),toJSStr(B(_7w(_jD,_jE,_jF))));return new F(function(){return _jw(_jz.b,_jA.b,_);});};switch(E(E(_jB.a).a)){case 0:return new F(function(){return _jC(_jj,_ji,_jh);});break;case 1:return new F(function(){return _jC(_jg,_jg,_jf);});break;case 2:return new F(function(){return _jC(_jj,_je,_ji);});break;case 3:return new F(function(){return _jC(_ji,_jj,_ji);});break;case 4:return new F(function(){return _jC(_ji,_ji,_jd);});break;case 5:return new F(function(){return _jC(_jd,_jc,_ie);});break;default:return E(_jb);}}}};return new F(function(){return _jw(_jn.b,_jo.b,_);});};switch(E(E(_jp.a).a)){case 0:return new F(function(){return _jq(_jj,_ji,_jh);});break;case 1:return new F(function(){return _jq(_jg,_jg,_jf);});break;case 2:return new F(function(){return _jq(_jj,_je,_ji);});break;case 3:return new F(function(){return _jq(_ji,_jj,_ji);});break;case 4:return new F(function(){return _jq(_ji,_ji,_jd);});break;case 5:return new F(function(){return _jq(_jd,_jc,_ie);});break;default:return E(_jb);}}}},_jH=0.72,_jI=0.44,_jJ=0.5,_jK=0.92,_jL=0.5900000000000001,_jM=0.8,_jN=1.01,_jO=1.42,_jP=0.52,_jQ=0.506,_jR=0.926,_jS=0.65,_jT=0.41200000000000003,_jU=0.762,_jV=1,_jW=function(_jX,_jY,_){var _jZ=E(_jX);if(!_jZ._){return _ic;}else{var _k0=E(_jY);if(!_k0._){return _ic;}else{var _k1=E(_jZ.a),_k2=function(_k3,_k4,_k5){var _k6=E(_id),_k7=__app2(_k6,B(_q(_4,_4,_4,B(_6(_k0.a,B(_ia(_k1.b)).c)))),toJSStr(B(_7w(_k3,_k4,_k5)))),_k8=function(_k9,_ka,_){var _kb=E(_k9);if(!_kb._){return _ic;}else{var _kc=E(_ka);if(!_kc._){return _ic;}else{var _kd=E(_kb.a),_ke=function(_kf,_kg,_kh){var _ki=__app2(_k6,B(_q(_4,_4,_4,B(_6(_kc.a,B(_ia(_kd.b)).c)))),toJSStr(B(_7w(_kf,_kg,_kh))));return new F(function(){return _k8(_kb.b,_kc.b,_);});};switch(E(E(_kd.a).a)){case 0:return new F(function(){return _ke(_jR,_jQ,_jP);});break;case 1:return new F(function(){return _ke(_jO,_jO,_jV);});break;case 2:return new F(function(){return _ke(_jN,_jM,_jL);});break;case 3:return new F(function(){return _ke(_jJ,_jK,_jJ);});break;case 4:return new F(function(){return _ke(_jI,_jI,_jH);});break;case 5:return new F(function(){return _ke(_jU,_jT,_jS);});break;default:return E(_jb);}}}};return new F(function(){return _k8(_jZ.b,_k0.b,_);});};switch(E(E(_k1.a).a)){case 0:return new F(function(){return _k2(_jR,_jQ,_jP);});break;case 1:return new F(function(){return _k2(_jO,_jO,_jV);});break;case 2:return new F(function(){return _k2(_jN,_jM,_jL);});break;case 3:return new F(function(){return _k2(_jJ,_jK,_jJ);});break;case 4:return new F(function(){return _k2(_jI,_jI,_jH);});break;case 5:return new F(function(){return _k2(_jU,_jT,_jS);});break;default:return E(_jb);}}}},_kj=function(_kk,_kl,_km,_kn,_ko){var _kp=new T(function(){var _kq=B(A1(_kl,new T3(0,_km,_kn,_ko))),_kr=E(_kq.a),_ks=E(_kq.b);return new T6(0,_kr.a,_kr.b,_kr.c,_ks.a,_ks.b,_ks.c);});return new T3(0,new T(function(){var _kt=E(_kk),_ku=E(_kp),_kv=_ku.d,_kw=E(_ku.a);if(_kt!=0){if(_kt<=0){return _kt*_kw+(1+_kt)*E(_kv);}else{return _kt*_kw+(1-_kt)*E(_kv);}}else{return _kt*_kw+E(_kv);}}),new T(function(){var _kx=E(_kk),_ky=E(_kp),_kz=_ky.e,_kA=E(_ky.b);if(_kx!=0){if(_kx<=0){return _kx*_kA+(1+_kx)*E(_kz);}else{return _kx*_kA+(1-_kx)*E(_kz);}}else{return _kx*_kA+E(_kz);}}),new T(function(){var _kB=E(_kk),_kC=E(_kp),_kD=_kC.f,_kE=E(_kC.c);if(_kB!=0){if(_kB<=0){return _kB*_kE+(1+_kB)*E(_kD);}else{return _kB*_kE+(1-_kB)*E(_kD);}}else{return _kB*_kE+E(_kD);}}));},_kF=function(_kG){var _kH=E(_kG),_kI=_kH.a,_kJ=_kH.b,_kK=_kH.c;return new T2(0,new T3(0,new T(function(){return 500-E(_kI);}),new T(function(){return 300+E(_kK);}),new T(function(){return E(_kJ)-500;})),new T3(0,new T(function(){return  -E(_kI)+500;}),new T(function(){return  -E(_kJ)+1000;}),_kK));},_kL=function(_kM,_kN,_kO){return new T2(0,new T3(0,new T(function(){return 500-E(_kM);}),new T(function(){return E(_kN)-500;}),new T(function(){return  -300-E(_kO);})),new T3(0,new T(function(){return  -E(_kM)+500;}),new T(function(){return  -E(_kN)-2000;}),new T(function(){return 180-E(_kO);})));},_kP=function(_kQ){var _kR=E(_kQ),_kS=B(_kL(_kR.a,_kR.b,_kR.c));return new T2(0,_kS.a,_kS.b);},_kT=function(_kU){return  -E(_kU);},_kV=function(_kW){var _kX=E(_kW),_kY=_kX.a,_kZ=_kX.b,_l0=_kX.c;return new T2(0,new T3(0,new T(function(){return  -300-E(_l0);}),new T(function(){return 500-E(_kZ);}),new T(function(){return 500-E(_kY);})),new T3(0,new T(function(){return  -E(_kY)-500;}),new T(function(){return B(_kT(_kZ));}),_l0));},_l1=function(_l2){var _l3=E(_l2),_l4=_l3.a,_l5=_l3.b,_l6=_l3.c;return new T2(0,new T3(0,new T(function(){return 300+E(_l6);}),new T(function(){return 500-E(_l5);}),new T(function(){return E(_l4)-500;})),new T3(0,new T(function(){return  -E(_l4)+1500;}),new T(function(){return B(_kT(_l5));}),_l6));},_l7=function(_l8){var _l9=E(_l8),_la=_l9.a,_lb=_l9.b,_lc=_l9.c;return new T2(0,new T3(0,new T(function(){return 500-E(_la);}),new T(function(){return  -300-E(_lc);}),new T(function(){return 500-E(_lb);})),new T3(0,new T(function(){return  -E(_la)+500;}),new T(function(){return  -E(_lb)-1000;}),_lc));},_ld=function(_le){var _lf=E(_le),_lg=_lf.a,_lh=_lf.b,_li=_lf.c;return new T2(0,new T3(0,new T(function(){return 500-E(_lg);}),new T(function(){return 500-E(_lh);}),new T(function(){return 300+E(_li);})),new T3(0,new T(function(){return  -E(_lg)+500;}),new T(function(){return B(_kT(_lh));}),_li));},_lj=function(_lk){return new T2(0,function(_ll){var _lm=E(_ll),_ln=B(_kj(_lk,_ld,_lm.a,_lm.b,_lm.c));return new T3(0,_ln.a,_ln.b,_ln.c);},new T2(1,function(_lo){var _lp=E(_lo),_lq=B(_kj(_lk,_l7,_lp.a,_lp.b,_lp.c));return new T3(0,_lq.a,_lq.b,_lq.c);},new T2(1,function(_lr){var _ls=E(_lr),_lt=B(_kj(_lk,_l1,_ls.a,_ls.b,_ls.c));return new T3(0,_lt.a,_lt.b,_lt.c);},new T2(1,function(_lu){var _lv=E(_lu),_lw=B(_kj(_lk,_kV,_lv.a,_lv.b,_lv.c));return new T3(0,_lw.a,_lw.b,_lw.c);},new T2(1,function(_lx){var _ly=E(_lx),_lz=B(_kj(_lk,_kP,_ly.a,_ly.b,_ly.c));return new T3(0,_lz.a,_lz.b,_lz.c);},new T2(1,function(_lA){var _lB=E(_lA),_lC=B(_kj(_lk,_kF,_lB.a,_lB.b,_lB.c));return new T3(0,_lC.a,_lC.b,_lC.c);},_5))))));},_lD=new T(function(){var _lE=B(_lj(_jV));return new T2(1,_lE.a,_lE.b);}),_lF=function(_lG,_lH){return E(_lG)==E(_lH);},_lI=function(_lJ,_lK){return new F(function(){return _lF(E(E(_lJ).a).a,E(E(_lK).a).a);});},_lL=function(_lM,_lN){var _lO=E(_lN);if(!_lO._){return __Z;}else{var _lP=_lO.a,_lQ=new T(function(){var _lR=B(_iN(new T(function(){return B(A1(_lM,_lP));}),_lO.b));return new T2(0,_lR.a,_lR.b);});return new T2(1,new T2(1,_lP,new T(function(){return E(E(_lQ).a);})),new T(function(){return B(_lL(_lM,E(_lQ).b));}));}},_lS=0,_lT=new T(function(){return B(unCStr("1101011011011100"));}),_lU=new T2(0,_lS,_lT),_lV=new T(function(){return B(unCStr("1010011000101101"));}),_lW=new T2(0,_lS,_lV),_lX=new T(function(){return B(unCStr("1101001101010010"));}),_lY=new T2(0,_lS,_lX),_lZ=new T(function(){return B(unCStr("0101010100100001"));}),_m0=new T2(0,_lS,_lZ),_m1=new T(function(){return B(unCStr("0010000110101101"));}),_m2=new T2(0,_lS,_m1),_m3=new T(function(){return B(unCStr("0101001000100010"));}),_m4=new T2(0,_lS,_m3),_m5=new T(function(){return B(unCStr("0101001000101101"));}),_m6=1,_m7=new T2(0,_m6,_m5),_m8=new T(function(){return B(unCStr("0001001000111101"));}),_m9=5,_ma=new T2(0,_m9,_m8),_mb=new T2(1,_ma,_5),_mc=new T(function(){return B(unCStr("1100010100101101"));}),_md=new T2(0,_m9,_mc),_me=new T2(1,_md,_mb),_mf=new T(function(){return B(unCStr("1110011011100010"));}),_mg=new T2(0,_m9,_mf),_mh=new T2(1,_mg,_me),_mi=new T(function(){return B(unCStr("1010010100110001"));}),_mj=new T2(0,_m9,_mi),_mk=new T2(1,_mj,_mh),_ml=new T(function(){return B(unCStr("1010010111000101"));}),_mm=new T2(0,_m9,_ml),_mn=new T2(1,_mm,_mk),_mo=new T(function(){return B(unCStr("0010001001010100"));}),_mp=new T2(0,_m9,_mo),_mq=new T2(1,_mp,_mn),_mr=new T(function(){return B(unCStr("0010001000100010"));}),_ms=4,_mt=new T2(0,_ms,_mr),_mu=new T2(1,_mt,_mq),_mv=new T(function(){return B(unCStr("0010110111010101"));}),_mw=new T2(0,_ms,_mv),_mx=new T2(1,_mw,_mu),_my=new T(function(){return B(unCStr("1101101011011010"));}),_mz=new T2(0,_ms,_my),_mA=new T2(1,_mz,_mx),_mB=new T(function(){return B(unCStr("0101101001010101"));}),_mC=new T2(0,_ms,_mB),_mD=new T2(1,_mC,_mA),_mE=new T(function(){return B(unCStr("0101110100100101"));}),_mF=new T2(0,_ms,_mE),_mG=new T2(1,_mF,_mD),_mH=new T2(0,_ms,_m3),_mI=new T2(1,_mH,_mG),_mJ=new T(function(){return B(unCStr("0010110110100010"));}),_mK=3,_mL=new T2(0,_mK,_mJ),_mM=new T2(1,_mL,_mI),_mN=new T(function(){return B(unCStr("0010110100100010"));}),_mO=new T2(0,_mK,_mN),_mP=new T2(1,_mO,_mM),_mQ=new T(function(){return B(unCStr("0101010101010010"));}),_mR=new T2(0,_mK,_mQ),_mS=new T2(1,_mR,_mP),_mT=new T(function(){return B(unCStr("0101001001010010"));}),_mU=new T2(0,_mK,_mT),_mV=new T2(1,_mU,_mS),_mW=new T(function(){return B(unCStr("0101110110100010"));}),_mX=new T2(0,_mK,_mW),_mY=new T2(1,_mX,_mV),_mZ=new T(function(){return B(unCStr("0101110110101101"));}),_n0=new T2(0,_mK,_mZ),_n1=new T2(1,_n0,_mY),_n2=new T(function(){return B(unCStr("1101001001011010"));}),_n3=2,_n4=new T2(0,_n3,_n2),_n5=new T2(1,_n4,_n1),_n6=new T(function(){return B(unCStr("0001101011010101"));}),_n7=new T2(0,_n3,_n6),_n8=new T2(1,_n7,_n5),_n9=new T(function(){return B(unCStr("0101010110100011"));}),_na=new T2(0,_n3,_n9),_nb=new T2(1,_na,_n8),_nc=new T(function(){return B(unCStr("0110001000110010"));}),_nd=new T2(0,_n3,_nc),_ne=new T2(1,_nd,_nb),_nf=new T(function(){return B(unCStr("1010110101001101"));}),_ng=new T2(0,_n3,_nf),_nh=new T2(1,_ng,_ne),_ni=new T(function(){return B(unCStr("0100001000100101"));}),_nj=new T2(0,_n3,_ni),_nk=new T2(1,_nj,_nh),_nl=new T(function(){return B(unCStr("1110001011010010"));}),_nm=new T2(0,_m6,_nl),_nn=new T2(1,_nm,_nk),_no=new T(function(){return B(unCStr("0010010100101101"));}),_np=new T2(0,_m6,_no),_nq=new T2(1,_np,_nn),_nr=new T(function(){return B(unCStr("0101001011000101"));}),_ns=new T2(0,_m6,_nr),_nt=new T2(1,_ns,_nq),_nu=new T(function(){return B(unCStr("0010001001010101"));}),_nv=new T2(0,_m6,_nu),_nw=new T2(1,_nv,_nt),_nx=new T(function(){return B(unCStr("1101101001011010"));}),_ny=new T2(0,_m6,_nx),_nz=new T2(1,_ny,_nw),_nA=new T2(1,_m7,_nz),_nB=new T2(1,_m4,_nA),_nC=new T2(1,_m2,_nB),_nD=new T2(1,_m0,_nC),_nE=new T2(1,_lY,_nD),_nF=new T2(1,_lW,_nE),_nG=new T2(1,_lU,_nF),_nH=function(_nI,_nJ,_nK){var _nL=E(_nJ);return new F(function(){return A2(_nI,_nL,new T(function(){return B(_nH(_nI,B(_C(_nL,_nK)),_nK));}));});},_nM=new T1(0,1),_nN=new T1(0,0),_nO=true,_nP=function(_nQ){return (E(_nQ)==49)?true:false;},_nR=new T1(0,6),_nS=new T(function(){return B(_36(_nR,_nN));}),_nT=function(_nU,_nV,_nW){var _nX=E(_nW);if(!_nX._){return __Z;}else{var _nY=new T(function(){var _nZ=E(_nX.a);return new T2(0,new T3(0,_nZ.a,_nO,new T(function(){if(!E(_nS)){return B(_5G(0,B(_3C(_nU,_nR)),_5));}else{return E(_35);}})),new T(function(){return B(_6(_nP,_nZ.b));}));});return new T2(1,_nY,new T(function(){return B(A1(_nV,_nX.b));}));}},_o0=new T(function(){return B(_nH(_nT,_nN,_nM));}),_o1=new T(function(){return B(A1(_o0,_nG));}),_o2=new T(function(){return B(_lL(_lI,_o1));}),_o3=function(_o4,_o5){var _o6=function(_o7){var _o8=E(_o7);if(!_o8._){return __Z;}else{return new F(function(){return _x(B(A1(_o4,_o8.a)),new T(function(){return B(_o6(_o8.b));},1));});}};return new F(function(){return _o6(_o5);});},_o9=new T(function(){return B(unCStr(": empty list"));}),_oa=function(_ob){return new F(function(){return err(B(_x(_de,new T(function(){return B(_x(_ob,_o9));},1))));});},_oc=new T(function(){return B(unCStr("head"));}),_od=new T(function(){return B(_oa(_oc));}),_oe=function(_of){var _og=E(_of);return (_og._==0)?E(_od):E(_og.a);},_oh=function(_oi,_oj){return (!E(_oi))?E(_oj):(!E(_oj))?true:false;},_ok=function(_ol,_om){return (!E(_ol))?(!E(_om))?true:false:E(_om);},_on=new T2(0,_ok,_oh),_oo=function(_op,_oq,_or){while(1){var _os=E(_oq);if(!_os._){return (E(_or)._==0)?true:false;}else{var _ot=E(_or);if(!_ot._){return false;}else{if(!B(A3(_6J,_op,_os.a,_ot.a))){return false;}else{_oq=_os.b;_or=_ot.b;continue;}}}}},_ou=function(_ov,_ow){return new F(function(){return _oo(_on,E(_ov).b,E(_ow).b);});},_ox=function(_oy,_oz){while(1){var _oA=E(_oz);if(!_oA._){return __Z;}else{var _oB=_oA.b,_oC=E(_oy);if(_oC==1){return E(_oB);}else{_oy=_oC-1|0;_oz=_oB;continue;}}}},_oD=function(_oE,_oF){var _oG=E(_oF);if(!_oG._){return __Z;}else{var _oH=_oG.a,_oI=E(_oE);return (_oI==1)?new T2(1,_oH,_5):new T2(1,_oH,new T(function(){return B(_oD(_oI-1|0,_oG.b));}));}},_oJ=function(_oK){return new F(function(){return _x(B(_ox(4,_oK)),new T(function(){return B(_oD(4,_oK));},1));});},_oL=function(_oM,_oN){if(!E(_oM)){return E(_oN);}else{var _oO=E(_oN);return false;}},_oP=function(_oQ,_oR){if(!E(_oQ)){var _oS=E(_oR);return true;}else{return E(_oR);}},_oT=function(_oU,_oV){if(!E(_oU)){var _oW=E(_oV);return false;}else{return (!E(_oV))?true:false;}},_oX=function(_oY,_oZ){if(!E(_oY)){return (!E(_oZ))?true:false;}else{var _p0=E(_oZ);return true;}},_p1=function(_p2,_p3){return (!E(_p2))?(!E(_p3))?1:0:(!E(_p3))?2:1;},_p4=function(_p5,_p6){if(!E(_p5)){return E(_p6);}else{var _p7=E(_p6);return true;}},_p8=function(_p9,_pa){if(!E(_p9)){var _pb=E(_pa);return false;}else{return E(_pa);}},_pc={_:0,a:_on,b:_p1,c:_oL,d:_oP,e:_oT,f:_oX,g:_p4,h:_p8},_pd=function(_pe){return E(E(_pe).b);},_pf=function(_pg,_ph,_pi){while(1){var _pj=E(_ph);if(!_pj._){return (E(_pi)._==0)?1:0;}else{var _pk=E(_pi);if(!_pk._){return 2;}else{var _pl=B(A3(_pd,_pg,_pj.a,_pk.a));if(_pl==1){_ph=_pj.b;_pi=_pk.b;continue;}else{return E(_pl);}}}}},_pm=function(_pn,_po){return new F(function(){return _pf(_pc,E(_pn).a,E(_po).a);});},_pp=function(_pq,_pr){while(1){var _ps=E(_pq);if(!_ps._){return E(_pr);}else{var _pt=new T2(1,_ps.a,_pr);_pq=_ps.b;_pr=_pt;continue;}}},_pu=function(_pv){return E(E(_pv).b);},_pw=new T2(1,_5,_5),_px=function(_py,_pz){var _pA=function(_pB,_pC){var _pD=E(_pB);if(!_pD._){return E(_pC);}else{var _pE=_pD.a,_pF=E(_pC);if(!_pF._){return E(_pD);}else{var _pG=_pF.a;return (B(A2(_py,_pE,_pG))==2)?new T2(1,_pG,new T(function(){return B(_pA(_pD,_pF.b));})):new T2(1,_pE,new T(function(){return B(_pA(_pD.b,_pF));}));}}},_pH=function(_pI){var _pJ=E(_pI);if(!_pJ._){return __Z;}else{var _pK=E(_pJ.b);return (_pK._==0)?E(_pJ):new T2(1,new T(function(){return B(_pA(_pJ.a,_pK.a));}),new T(function(){return B(_pH(_pK.b));}));}},_pL=new T(function(){return B(_pM(B(_pH(_5))));}),_pM=function(_pN){while(1){var _pO=E(_pN);if(!_pO._){return E(_pL);}else{if(!E(_pO.b)._){return E(_pO.a);}else{_pN=B(_pH(_pO));continue;}}}},_pP=new T(function(){return B(_pQ(_5));}),_pR=function(_pS,_pT,_pU){while(1){var _pV=B((function(_pW,_pX,_pY){var _pZ=E(_pY);if(!_pZ._){return new T2(1,new T2(1,_pW,_pX),_pP);}else{var _q0=_pZ.a;if(B(A2(_py,_pW,_q0))==2){var _q1=new T2(1,_pW,_pX);_pS=_q0;_pT=_q1;_pU=_pZ.b;return __continue;}else{return new T2(1,new T2(1,_pW,_pX),new T(function(){return B(_pQ(_pZ));}));}}})(_pS,_pT,_pU));if(_pV!=__continue){return _pV;}}},_q2=function(_q3,_q4,_q5){while(1){var _q6=B((function(_q7,_q8,_q9){var _qa=E(_q9);if(!_qa._){return new T2(1,new T(function(){return B(A1(_q8,new T2(1,_q7,_5)));}),_pP);}else{var _qb=_qa.a,_qc=_qa.b;switch(B(A2(_py,_q7,_qb))){case 0:_q3=_qb;_q4=function(_qd){return new F(function(){return A1(_q8,new T2(1,_q7,_qd));});};_q5=_qc;return __continue;case 1:_q3=_qb;_q4=function(_qe){return new F(function(){return A1(_q8,new T2(1,_q7,_qe));});};_q5=_qc;return __continue;default:return new T2(1,new T(function(){return B(A1(_q8,new T2(1,_q7,_5)));}),new T(function(){return B(_pQ(_qa));}));}}})(_q3,_q4,_q5));if(_q6!=__continue){return _q6;}}},_pQ=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_pw);}else{var _qh=_qg.a,_qi=E(_qg.b);if(!_qi._){return new T2(1,_qg,_5);}else{var _qj=_qi.a,_qk=_qi.b;if(B(A2(_py,_qh,_qj))==2){return new F(function(){return _pR(_qj,new T2(1,_qh,_5),_qk);});}else{return new F(function(){return _q2(_qj,function(_ql){return new T2(1,_qh,_ql);},_qk);});}}}};return new F(function(){return _pM(B(_pQ(_pz)));});},_qm=new T(function(){return B(unCStr("tail"));}),_qn=new T(function(){return B(_oa(_qm));}),_qo=function(_qp){var _qq=E(_qp);return (_qq._==0)?E(_qn):E(_qq.b);},_qr=function(_qs,_qt,_qu,_qv){var _qw=new T3(0,_qs,_qt,_qu),_qx=new T(function(){var _qy=new T(function(){if(!E(_qt)){return true;}else{return false;}}),_qz=function(_qA,_qB){var _qC=new T2(1,new T(function(){var _qD=E(_qA);if(!_qD._){return E(_od);}else{return E(_qD.a);}}),new T(function(){return B(_pp(B(_qo(_qA)),_5));}));return new T2(1,new T2(0,_qC,new T2(0,new T3(0,_qs,_qy,_qu),_qC)),_qB);},_qE=function(_qF,_qG){var _qH=E(_qG);if(_qH==1){return new F(function(){return _qz(_qF,_5);});}else{var _qI=new T(function(){return B(_qE(new T(function(){return B(_oJ(_qF));}),_qH-1|0));});return new F(function(){return _qz(_qF,_qI);});}};return B(_qE(_qv,4));}),_qJ=function(_qK,_qL){var _qM=E(_qL);if(_qM==1){return new T2(1,new T(function(){var _qN=E(_qK);return new T2(0,_qN,new T2(0,_qw,_qN));}),_qx);}else{var _qO=new T(function(){return B(_qJ(new T(function(){return B(_oJ(_qK));}),_qM-1|0));});return new T2(1,new T(function(){var _qP=E(_qK);return new T2(0,_qP,new T2(0,_qw,_qP));}),_qO);}};return new F(function(){return _6(_oe,B(_lL(_ou,B(_6(_pu,B(_px(_pm,B(_qJ(_qv,4)))))))));});},_qQ=function(_qR){var _qS=E(_qR),_qT=E(_qS.a);return new F(function(){return _qr(_qT.a,_qT.b,_qT.c,_qS.b);});},_qU=function(_qV){return new F(function(){return _o3(_qQ,_qV);});},_qW=new T(function(){var _qX=E(_o2);if(!_qX._){return E(_qn);}else{return B(_6(_qU,_qX.b));}}),_qY=function(_qZ,_r0){return new F(function(){return _dp(_qZ,E(_r0));});},_r1=function(_r2){var _r3=E(_r2);if(!_r3._){return __Z;}else{var _r4=_r3.a,_r5=_r3.b,_r6=new T(function(){return B(_6(function(_r7){var _r8=E(_r7);return new T2(0,_r8.a,new T2(1,_r4,_r8.b));},B(_r1(_r5))));});return new T2(1,new T2(0,_r4,_r5),_r6);}},_r9=1,_ra=2,_rb=3,_rc=4,_rd=new T2(1,_rc,_5),_re=new T2(1,_rb,_rd),_rf=new T2(1,_ra,_re),_rg=new T2(1,_r9,_rf),_rh=0,_ri=new T2(1,_rh,_rg),_rj=5,_rk=6,_rl=7,_rm=8,_rn=new T2(1,_rm,_5),_ro=new T2(1,_rl,_rn),_rp=new T2(1,_rk,_ro),_rq=new T2(1,_rj,_rp),_rr=new T2(1,_rc,_rq),_rs=9,_rt=10,_ru=11,_rv=12,_rw=new T2(1,_rv,_5),_rx=new T2(1,_ru,_rw),_ry=new T2(1,_rt,_rx),_rz=new T2(1,_rs,_ry),_rA=new T2(1,_rm,_rz),_rB=13,_rC=14,_rD=15,_rE=new T2(1,_rh,_5),_rF=new T2(1,_rD,_rE),_rG=new T2(1,_rC,_rF),_rH=new T2(1,_rB,_rG),_rI=new T2(1,_rv,_rH),_rJ=new T2(1,_rI,_5),_rK=new T2(1,_rA,_rJ),_rL=new T2(1,_rr,_rK),_rM=new T2(1,_ri,_rL),_rN=function(_rO){var _rP=function(_qV){return new F(function(){return _qY(E(_rO).b,_qV);});};return new F(function(){return _6(function(_qV){return new F(function(){return _6(_rP,_qV);});},_rM);});},_rQ=function(_rR){while(1){var _rS=E(_rR);if(!_rS._){return true;}else{if(!E(_rS.a)){return false;}else{_rR=_rS.b;continue;}}}},_rT=function(_rU){while(1){var _rV=E(_rU);if(!_rV._){return true;}else{if(!E(_rV.a)){return false;}else{_rU=_rV.b;continue;}}}},_rW=function(_rX){while(1){var _rY=E(_rX);if(!_rY._){return true;}else{if(!E(_rY.a)){return false;}else{_rX=_rY.b;continue;}}}},_rZ=function(_s0,_s1){var _s2=E(_s1);return new F(function(){return A2(_s0,_s2.a,_s2.b);});},_s3=function(_s4,_s5){return true;},_s6=new T2(1,_s3,_5),_s7=new T2(1,_oh,_s6),_s8=new T2(1,_oh,_s7),_s9=new T2(1,_oh,_s8),_sa=new T2(1,_s3,_s9),_sb=function(_sc,_sd){var _se=E(_sc);if(!_se._){return __Z;}else{var _sf=E(_sd);return (_sf._==0)?__Z:new T2(1,new T2(0,_se.a,_sf.a),new T(function(){return B(_sb(_se.b,_sf.b));}));}},_sg=function(_sh,_si,_sj,_sk){var _sl=function(_sm){if(E(_sm)==1){if(!B(_rT(B(_ei(_rZ,_sa,new T(function(){return B(_sb(_sh,_si));},1)))))){return false;}else{return new F(function(){return _rW(B(_ei(_rZ,_sa,new T(function(){return B(_sb(_sj,_sk));},1))));});}}else{return false;}};if(!B(_dp(_sh,0))){if(!B(_dp(_si,0))){if(!B(_dp(_sj,0))){return new F(function(){return _sl(0);});}else{return new F(function(){return _sl(1);});}}else{if(!B(_dp(_sj,0))){return new F(function(){return _sl(1);});}else{return new F(function(){return _sl(2);});}}}else{if(!B(_dp(_si,0))){if(!B(_dp(_sj,0))){return new F(function(){return _sl(1);});}else{return new F(function(){return _sl(2);});}}else{if(!B(_dp(_sj,0))){return new F(function(){return _sl(2);});}else{return new F(function(){return _sl(3);});}}}},_sn=function(_so){return new F(function(){return _j9("Solver.hs:(111,1)-(117,106)|function possibilities5");});},_sp=new T(function(){return B(_sn(_));}),_sq=function(_sr,_ss){return (!E(_sr))?true:(!E(_ss))?true:false;},_st=new T2(1,_sq,_5),_su=new T2(1,_oh,_st),_sv=new T2(1,_oh,_su),_sw=new T2(1,_oh,_sv),_sx=new T2(1,_sq,_sw),_sy=function(_sz,_sA){var _sB=new T(function(){return B(_dp(B(_rN(_sz)),0));}),_sC=new T(function(){return B(_pp(_sB,_5));}),_sD=new T(function(){return B(_pp(B(_dp(B(_rN(_sz)),1)),_5));}),_sE=new T(function(){return B(_dp(B(_rN(_sz)),3));}),_sF=new T(function(){return B(_pp(B(_dp(B(_rN(_sz)),2)),_5));}),_sG=function(_sH){var _sI=E(_sH);if(!_sI._){return __Z;}else{var _sJ=E(_sI.a),_sK=new T(function(){return B(_r1(_sJ.b));}),_sL=new T(function(){return B(_sG(_sI.b));}),_sM=function(_sN){while(1){var _sO=B((function(_sP){var _sQ=E(_sP);if(!_sQ._){return E(_sL);}else{var _sR=_sQ.a,_sS=_sQ.b,_sT=new T(function(){var _sU=new T(function(){var _sV=function(_qV){return new F(function(){return _qY(E(_sR).b,_qV);});};return B(_dp(B(_6(function(_qV){return new F(function(){return _6(_sV,_qV);});},_rM)),0));},1);return B(_sb(_sF,_sU));},1);if(!B(_rQ(B(_ei(_rZ,_sx,_sT))))){_sN=_sS;return __continue;}else{var _sW=new T(function(){return B(_dp(B(_rN(_sR)),2));}),_sX=new T(function(){return B(_pp(_sW,_5));}),_sY=new T(function(){return B(_dp(B(_rN(_sR)),1));}),_sZ=new T(function(){return B(_pp(B(_dp(B(_rN(_sR)),3)),_5));}),_t0=new T(function(){return B(_sM(_sS));}),_t1=function(_t2){var _t3=E(_t2);if(!_t3._){return E(_t0);}else{var _t4=E(_t3.a),_t5=new T(function(){return B(_r1(_t4.b));}),_t6=new T(function(){return B(_t1(_t3.b));}),_t7=function(_t8){while(1){var _t9=B((function(_ta){var _tb=E(_ta);if(!_tb._){return E(_t6);}else{var _tc=_tb.a,_td=_tb.b;if(!B(_sg(_sE,B(_pp(B(_dp(B(_rN(_tc)),1)),_5)),_sZ,new T(function(){return B(_dp(B(_rN(_tc)),2));},1)))){_t8=_td;return __continue;}else{var _te=new T(function(){return B(_dp(B(_rN(_tc)),0));}),_tf=new T(function(){return B(_pp(B(_dp(B(_rN(_tc)),0)),_5));}),_tg=new T(function(){return B(_dp(B(_rN(_tc)),3));}),_th=new T(function(){return B(_t7(_td));}),_ti=function(_tj){var _tk=E(_tj);if(!_tk._){return E(_th);}else{var _tl=E(_tk.a),_tm=new T(function(){return B(_r1(_tl.b));}),_tn=new T(function(){return B(_ti(_tk.b));}),_to=function(_tp){while(1){var _tq=B((function(_tr){var _ts=E(_tr);if(!_ts._){return E(_tn);}else{var _tt=_ts.a,_tu=_ts.b;if(!B(_sg(_sD,B(_dp(B(_rN(_tt)),3)),_sY,new T(function(){return B(_pp(B(_dp(B(_rN(_tt)),2)),_5));},1)))){_tp=_tu;return __continue;}else{var _tv=new T(function(){return B(_dp(B(_rN(_tt)),0));}),_tw=new T(function(){return B(_pp(_tv,_5));}),_tx=new T(function(){return B(_pp(B(_dp(B(_rN(_tt)),1)),_5));}),_ty=new T(function(){return B(_to(_tu));}),_tz=function(_tA){var _tB=E(_tA);if(!_tB._){return E(_ty);}else{var _tC=E(_tB.a),_tD=new T(function(){return B(_tz(_tB.b));}),_tE=function(_tF){while(1){var _tG=B((function(_tH){var _tI=E(_tH);if(!_tI._){return E(_tD);}else{var _tJ=_tI.a,_tK=_tI.b;if(!B(_sg(_sX,B(_dp(B(_rN(_tJ)),0)),_tg,new T(function(){return B(_pp(B(_dp(B(_rN(_tJ)),3)),_5));},1)))){_tF=_tK;return __continue;}else{if(!B(_sg(_sW,B(_pp(B(_dp(B(_rN(_tJ)),0)),_5)),_tx,new T(function(){return B(_dp(B(_rN(_tJ)),1));},1)))){_tF=_tK;return __continue;}else{var _tL=E(_tC.b);if(!_tL._){return E(_sp);}else{var _tM=_tL.a;if(!E(_tL.b)._){var _tN=new T(function(){return B(_dp(B(_rN(_tJ)),2));}),_tO=new T(function(){return B(_pp(_tN,_5));}),_tP=new T(function(){var _tQ=function(_tR){while(1){var _tS=B((function(_tT){var _tU=E(_tT);if(!_tU._){return E(_tD);}else{var _tV=_tU.a,_tW=_tU.b;if(!B(_sg(_sX,B(_dp(B(_rN(_tV)),0)),_tg,new T(function(){return B(_pp(B(_dp(B(_rN(_tV)),3)),_5));},1)))){_tR=_tW;return __continue;}else{if(!B(_sg(_sW,B(_pp(B(_dp(B(_rN(_tV)),0)),_5)),_tx,new T(function(){return B(_dp(B(_rN(_tV)),1));},1)))){_tR=_tW;return __continue;}else{var _tX=new T(function(){return B(_dp(B(_rN(_tV)),2));}),_tY=new T(function(){return B(_pp(_tX,_5));}),_tZ=new T(function(){return B(_tQ(_tW));}),_u0=function(_u1){while(1){var _u2=B((function(_u3){var _u4=E(_u3);if(!_u4._){return E(_tZ);}else{var _u5=_u4.a,_u6=_u4.b;if(!B(_sg(_tY,B(_dp(B(_rN(_u5)),0)),_te,new T(function(){return B(_pp(B(_dp(B(_rN(_u5)),3)),_5));},1)))){_u1=_u6;return __continue;}else{if(!B(_sg(_tw,B(_dp(B(_rN(_u5)),1)),_tX,new T(function(){return B(_pp(B(_dp(B(_rN(_u5)),0)),_5));},1)))){_u1=_u6;return __continue;}else{if(!B(_sg(_sC,B(_dp(B(_rN(_u5)),2)),_tv,new T(function(){return B(_pp(B(_dp(B(_rN(_u5)),1)),_5));},1)))){_u1=_u6;return __continue;}else{if(!B(_sg(_tf,B(_dp(B(_rN(_u5)),3)),_sB,new T(function(){return B(_pp(B(_dp(B(_rN(_u5)),2)),_5));},1)))){_u1=_u6;return __continue;}else{return new T2(1,new T2(1,_sR,new T2(1,_tc,new T2(1,_tt,new T2(1,_tV,new T2(1,_u5,_5))))),new T(function(){return B(_u0(_u6));}));}}}}}})(_u1));if(_u2!=__continue){return _u2;}}};return new F(function(){return _u0(_tM);});}}}})(_tR));if(_tS!=__continue){return _tS;}}};return B(_tQ(_tK));}),_u7=function(_u8){while(1){var _u9=B((function(_ua){var _ub=E(_ua);if(!_ub._){return E(_tP);}else{var _uc=_ub.a,_ud=_ub.b;if(!B(_sg(_tO,B(_dp(B(_rN(_uc)),0)),_te,new T(function(){return B(_pp(B(_dp(B(_rN(_uc)),3)),_5));},1)))){_u8=_ud;return __continue;}else{if(!B(_sg(_tw,B(_dp(B(_rN(_uc)),1)),_tN,new T(function(){return B(_pp(B(_dp(B(_rN(_uc)),0)),_5));},1)))){_u8=_ud;return __continue;}else{if(!B(_sg(_sC,B(_dp(B(_rN(_uc)),2)),_tv,new T(function(){return B(_pp(B(_dp(B(_rN(_uc)),1)),_5));},1)))){_u8=_ud;return __continue;}else{if(!B(_sg(_tf,B(_dp(B(_rN(_uc)),3)),_sB,new T(function(){return B(_pp(B(_dp(B(_rN(_uc)),2)),_5));},1)))){_u8=_ud;return __continue;}else{return new T2(1,new T2(1,_sR,new T2(1,_tc,new T2(1,_tt,new T2(1,_tJ,new T2(1,_uc,_5))))),new T(function(){return B(_u7(_ud));}));}}}}}})(_u8));if(_u9!=__continue){return _u9;}}};return new F(function(){return _u7(_tM);});}else{return E(_sp);}}}}}})(_tF));if(_tG!=__continue){return _tG;}}};return new F(function(){return _tE(_tC.a);});}};return new F(function(){return _tz(_tm);});}}})(_tp));if(_tq!=__continue){return _tq;}}};return new F(function(){return _to(_tl.a);});}};return new F(function(){return _ti(_t5);});}}})(_t8));if(_t9!=__continue){return _t9;}}};return new F(function(){return _t7(_t4.a);});}};return new F(function(){return _t1(_sK);});}}})(_sN));if(_sO!=__continue){return _sO;}}};return new F(function(){return _sM(_sJ.a);});}};return new F(function(){return _sG(B(_r1(_sA)));});},_ue=function(_uf){var _ug=E(_uf);if(!_ug._){return __Z;}else{var _uh=_ug.a,_ui=new T(function(){return B(_ue(_ug.b));}),_uj=function(_uk){var _ul=E(_uk);return (_ul._==0)?E(_ui):new T2(1,new T2(1,_uh,_ul.a),new T(function(){return B(_uj(_ul.b));}));};return new F(function(){return _uj(B(_sy(_uh,_qW)));});}},_um=new T(function(){var _un=E(_o2);if(!_un._){return E(_od);}else{return B(_ue(_un.a));}}),_uo=new T(function(){var _up=E(_um);if(!_up._){return E(_od);}else{return E(_up.a);}}),_uq=function(_ur,_us,_){var _ut=E(_ur);if(!_ut._){return _ic;}else{var _uu=E(_us);if(!_uu._){return _ic;}else{var _uv=E(_ut.a),_uw=function(_ux,_uy,_uz){var _uA=E(_id),_uB=__app2(_uA,B(_q(_4,_4,_4,B(_6(_uu.a,B(_ia(_uv.b)).b)))),toJSStr(B(_7w(_ux,_uy,_uz)))),_uC=function(_uD,_uE,_){var _uF=E(_uD);if(!_uF._){return _ic;}else{var _uG=E(_uE);if(!_uG._){return _ic;}else{var _uH=E(_uF.a),_uI=function(_uJ,_uK,_uL){var _uM=__app2(_uA,B(_q(_4,_4,_4,B(_6(_uG.a,B(_ia(_uH.b)).b)))),toJSStr(B(_7w(_uJ,_uK,_uL))));return new F(function(){return _uC(_uF.b,_uG.b,_);});};switch(E(E(_uH.a).a)){case 0:return new F(function(){return _uI(_jj,_ji,_jh);});break;case 1:return new F(function(){return _uI(_jg,_jg,_jf);});break;case 2:return new F(function(){return _uI(_jj,_je,_ji);});break;case 3:return new F(function(){return _uI(_ji,_jj,_ji);});break;case 4:return new F(function(){return _uI(_ji,_ji,_jd);});break;case 5:return new F(function(){return _uI(_jd,_jc,_ie);});break;default:return E(_jb);}}}};return new F(function(){return _uC(_ut.b,_uu.b,_);});};switch(E(E(_uv.a).a)){case 0:return new F(function(){return _uw(_jj,_ji,_jh);});break;case 1:return new F(function(){return _uw(_jg,_jg,_jf);});break;case 2:return new F(function(){return _uw(_jj,_je,_ji);});break;case 3:return new F(function(){return _uw(_ji,_jj,_ji);});break;case 4:return new F(function(){return _uw(_ji,_ji,_jd);});break;case 5:return new F(function(){return _uw(_jd,_jc,_ie);});break;default:return E(_jb);}}}},_uN=function(_){var _uO=B(_uq(_uo,_lD,_)),_uP=B(_jW(_uo,_lD,_));return new F(function(){return _jk(_uo,_lD,_);});},_uQ=function(_){return new F(function(){return _uN(_);});};
var hasteMain = function() {B(A(_uQ, [0]));};wandow.onload = hasteMain;
hasteMain();
})();
