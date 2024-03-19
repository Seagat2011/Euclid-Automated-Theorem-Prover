/*

    TITLE
    Object.js

    AUTHOR
    Seagat2011 www.gitub.com/Seagat2011
    eterna.cmu.edu/web/player/90270/
    fold.it/port/user/1992490

    VERSION
    Major.Minor.Bugfix.Patch
    1.0.0.0

    DESCRIPTION
    Properties file

    UPDATED

    STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

    REFERENCES

    COMPATIBILITY
    Chrome 53+

*/
Object.prototype.last = function(){
  var i = this.length-1
  return this[i]
}
Object.prototype.toRegExp=function(flags){
  var self = this
  var w = self.replace(/([\.\+\-\*\?\{\}\[\]\|\\]+)/g,'\\$1')
  var u = new RegExp(`^${w} | ${w} | ${w}$`,flags)
  return u
}
Object.prototype.mylog = function(){
    var i,I = arguments.length
    var self = this
    this.innerText = ""
    for(i=0;i<I;i++){
        self.innerText += (arguments[i]).toString() + "\n"
    }
}
Object.prototype.clear=function(){
    var self=this
    self.innerHTML = self.innerText = self.textBuffer=""
}
Object.prototype.show=function(){
    var self=this
    self.style.display = 'inline'
}
Object.prototype.hide=function(){
    var self=this
    self.style.display = 'none'
}

function _Chrome_ScollAsNeeded(){
    var self = this;

    self.scrollIntoViewIfNeeded();
}
function _Firefox_ScollAsNeeded(){
    var self = this;

    // 'scrollIntoViewIfNeeded' is not standard and not supported by Firefox. //
    // For browsers, like Firefox, we'll use a fallback approach. //
    const rect = self.getBoundingClientRect();

    if (rect.bottom > window.innerHeight || rect.top < 0) {
        // If element is not fully visible, use 'scrollIntoView' with 'block: nearest'
        // to scroll the minimum amount needed to bring the element into view.
        self.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    }

    // If the element is fully visible, no action is taken. //
}

// 'scrollIntoViewIfNeeded' is not standard and not supported by Firefox. //
// Hence, we'll first check if it's available. //
const isNotChrome_Flag = !/Chrome/.test(navigator.userAgent);

Object.prototype.scrollIntoViewIfNeeded = isNotChrome_Flag 
    ? _Firefox_ScollAsNeeded
    : _Chrome_ScollAsNeeded ;

Object.prototype.appendlogR = 
Object.prototype.appendlogRaw = function(args,bRender){
    var self=this;
    self.textBuffer || (self.textBuffer=[]);
    args && self.textBuffer.push(...args.split(/<br>|<hr>/g).filter((u)=>{ return u!='' }))
    if(bRender){
        self.textBuffer && render({ src:entag(self.textBuffer.join('\n')),targ:self })
        self.innerHTML+='<br><hr>'
        self.scrollIntoViewIfNeeded();
        self.textBuffer=[];
    }
}
Object.prototype.appendlog = function(){
  var I = arguments.length
  var self = this
  var z=[]
  for(var i=0;i<I;i++){
    z.push( "<br>" + (arguments[i]).toString() + "<br>" )
  }
  self.innerHTML += z.join('<br>')
  self.scrollIntoViewIfNeeded();
}
Object.prototype.startsWith = function(re){
  return this.toString().match(new RegExp("^"+re))
}
Object.prototype.empty = function(){
  this.length = 0
}
Object.prototype.forEach = function(cb){
    var self=this
    for(o in self){
        if(self.hasOwnProperty(o)){
          self[o] = cb(o,self[o],self)
        }
    }
}
Object.prototype.deepCopy = function(obj) {
    if (obj === null || typeof obj !== 'object') {
        return obj;
    }

    if (obj instanceof Array) {
        let copy = [];
        for (let attr in obj) {
            if (obj.hasOwnProperty(attr)) copy[attr] = deepCopy(obj[attr]);
        }
        return copy;
    }

    if (obj instanceof Object) {
        let copy = {};
        for (let attr in obj) {
            if (obj.hasOwnProperty(attr)) copy[attr] = deepCopy(obj[attr]);
        }
        return copy;
    }

    throw new Error("Unable to copy obj! Its type is not supported.");
}
Object.prototype.shallowCopy = function(){
    var w = this;
    var obj = JSON.parse(JSON.stringify(w));
    return obj;
}
Object.prototype.clonePROPS = function(){
    var self=this
    var args={}
    for(var w of arguments){
        args[w]=self[w]
    }
    return args
}
Object.prototype.isSquare_NewtonRaphsonMethod = function(n){
    if (n < 0n) return false;
    if (n < 2n) return true;
  
    let x = n / 2n;
    let y = (x + n / x) / 2n;
    while (y < x) {
      x = y;
      y = (x + n / x) / 2n;
    }
    return x * x === n;
}
Object.prototype.isSquare = function(n){
    if (n < 0n) return false;
    if (n < 2n) return true;
    let low = 0n, high = n;

    while (low <= high) {
        let mid = (low + high) >> 1n;
        let square = mid * mid;

        if (square < n) {
            low = mid + 1n;
        } else if (square > n) {
            high = mid - 1n;
        } else {
            return true;
        }
    }
    return false;
}
Object.prototype.isaTentativeProof=function(u){
    ret = false;
    const w=this;
    var val=(w/('=').asPrimaryKey());
    var ProofFound_Flag=self.isSquare_NewtonRaphsonMethod(val);
    if(ProofFound_Flag){
        ret = `<br><br>Q.E.D. (via ${u})<br><hr>`;
    }
    return ret;
}
Object.prototype.solutionComplete = function(u){
    var obj = this.join(" ").stripWhiteSpace().split(/\s+=\s+/)
    var result = obj[0]
    if(obj.length<2){
        result=""
    } else {
        result = obj[0]
        for(var w of obj){
            var quickCheckfFailed = (result.length != w.length)
            var proofFailed = (result != w)
            if(quickCheckfFailed || proofFailed){
                  result = ""
                  break
            }
        }
        if(result){
            g_SOLVED = result = `<br><br>Q.E.D. (via ${u})<br><hr>`;
        }
    }
    return result
}
Object.prototype.tokenizeSTRING=function(delim){
    var self=this
    var delim = delim || ' '
    var ret=self.split( delim )
    return ret
}
Object.prototype.RepackAsString=function(){
    var self=this
    var ret=self.Repack().join(' ')
    return ret
}
Object.prototype.RepackAsStringThenRetokenize=function(){
    var self=this
    var ret=self.RepackAsString().split(' ')
    return ret
}
Object.prototype.getLines = function(){
  return this.toString().replace(/^\n*|\n*$/,"").split(/\n/g)
}
Object.prototype._init = false
Object.prototype.init = function(){
    return this._init
}
Object.prototype.build = function(u){
  var w
  var lemma
  var self = this
  self.Libraries = self.lib.innerText.getLines()
  var s = self.axm.innerText
    .replace(/\n+/g,'\n')
    .replace(/~=/g,'=')
    .split(/\n.*Prove[\s\t:]*/)
  self.compileAtomics(s[0].getLines())
  if(self.edt.id==self.axm.id){
    lemma = s[1]
    w = lemma.split(/\s+=\s+/g)
  } else { // debug mode //
    lemma = self.edt.innerText
    w = self.edt.innerText.split(/\s+=\s+/g)
  }
  self.Theorem = {
    lhs:w[0],
    rhs:w[1],
    lemma:lemma.split(/\s+/g),
  }
  self.optimizeCallGraph()
  self._init = true
}
Object.prototype.optimizeCallGraph=function(){
    var self = this
    var guidROOT = 'axiomROOT'
    var TheoremSUBKEY = self.Theorem.lemma.asPrimaryKey()
    self.map((u,i,me)=>{
        var uGUID = u._guid;
        TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY) ? (u._lhsCallGraph[guidROOT]=true) : "" ;
        TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY) ? (u._rhsCallGraph[guidROOT]=true) : "" ;
        self.map((v,j,too)=>{
            if(i!=j){
                (u._rhsSUBKEY.subkeyFOUND(v._lhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._lhsSUBKEY)) ? (v._lhsCallGraph[uGUID]=true) : "" ;
                (u._rhsSUBKEY.subkeyFOUND(v._rhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._rhsSUBKEY)) ? (v._rhsCallGraph[uGUID]=true) : "" ;
            }
            return v
        });
        return u
    });
}
Object.prototype.stripWhiteSpace = function(){
  return this.replace(/^\s+|\s+$/,"").replace(/\s+/g," ")
}
Object.prototype.deepSplit = function(){
    var u
    var self = this
    u = self.split(/\s+/g)
    return u
}
Object.prototype.collapseRedundantPaths = function(){
    var self = this
    var redundancyFound
    var buff={}
    self.map((u,K,me)=>{
        if(u in buff){
            var k=buff[u]
            for(var j=k;j<K;j++){
                delete buff[ me[j] ]
                me[j]=''
            }
        }
        buff[u]=K
        return u
    });
    var tmp=self.filter((u)=>{ return (u != '') })
    return tmp
}
Object.prototype.collapseEmptyCells = function(u){
    var self = this
    var tmp=[];
    self.map(a=>{
        if(a)
            tmp.push(...a.split(' '))
        return a
    })
    return tmp
}
Object.prototype.compileAtomics = function(a){
    var self = this
    var j=0
    var k=0
    a && a.map((u,i,me)=>{
        if(Boolean(u.match(/<==|==>/))){
            j++
            self.compileLemmas(u.stripWhiteSpace(),i)
        } else {
            k++
            self.compileAxioms(u.stripWhiteSpace(),i)
        }
    });
}
Object.prototype.compileLemmas = function(v,idx){
    var self = this
    u=v.split(/,/)[0]
    var axiom_any = Boolean(u.match(/<==>/));
    u.split(/\s+<?=+>?\s+/)
    .map((_u,ii,me)=>{
        if(ii%2==0){
            var _i=me[ii]
            var _j=me[(ii+1)]
            var w = (_i.length < _j.length) ? [_i,_j] : [_j,_i] ;
            var guid=self.length
            self.push(new _AXIOM_
            ({
                _guid:"axiom_"+guid,
                _id:guid,
                _rhs:w[0],
                _lhs:w[1],
                _stack:[],
                _flags:'Lemma',
                _isOnline:true,
                _rhsCallGraph:{},
                _lhsCallGraph:{},
                _rhsSUBKEY:w[0].asPrimaryKey(),
                _lhsSUBKEY:w[1].asPrimaryKey(),
                _history:{ _reduce:{},_expand:{} },
                _false:"68934A3E9455FA72420237EB05902327",
                _basenetFOUND:"68934A3E9455FA72420237EB05902327",
            })
            );
        }
    });
}
Object.prototype.compileAxioms = function(v,idx){
    var self = this;
    u=v.split(/,/)[0]
    var _u = u.split(/\s+\=\s+/)
    var w = (_u[0].length < _u[1].length) ? [_u[0],_u[1]] : [_u[1],_u[0]] ;
    var guid=self.length
    self.push(new _AXIOM_
    ({
        _guid:"axiom_"+guid,
        _id:guid,
        _rhs:w[0],
        _lhs:w[1],
        _stack:[],
        _isOnline:true,
        _rhsCallGraph:{},
        _lhsCallGraph:{},
        _rhsSUBKEY:w[0].asPrimaryKey(),
        _lhsSUBKEY:w[1].asPrimaryKey(),
        _history:{ _reduce:{},_expand:{} },
        _false:"68934A3E9455FA72420237EB05902327",
        _basenetFOUND:"68934A3E9455FA72420237EB05902327",
    })
    );
}
Object.prototype.attachSourceEditor = function(){
  var self = this
  var args = arguments[0]
  args.forEach(function(w){
    self[w] = args[w]
    return w
  })
}
Object.prototype.addTAG = function(s){
  return "<"+s+">("+this.toString()+")</"+s+">"
}

Object.prototype.keysMatch = function(){
    var key=this.join(' ').split(/\s*=\s*/)
    var KEYSMATCH=Boolean(key.length && key.length>1 && (key[0].asPrimaryKey()==key[1].asPrimaryKey()))
    return KEYSMATCH
}
Object.prototype.subkeyFOUND=function(v){
    var u=this
    var ret=((u%v)==0)
    return ret
}
Object.prototype.subkeyUPDATE=function(from,to){
    var self=this
    var ret=(self/from*to)
    return ret
}
var PRIMARYKEY = {}
var LASTPRIMEIDX = BigInt(3)
Object.prototype.isPrime=function(num) {
    if (num <= BigInt(1)) return false;
    if (num <= BigInt(3)) return true;
  
    // Check divisibility from 2 to the square root of num
    for (let i = BigInt(2); i * i <= num; ++i) { 
      if (num % i === 0) return false;
    }
    return true;
}
Object.prototype.nextPrime=function() {
    var num = LASTPRIMEIDX;
    while (1) {
      if (isPrime(num)) {
        LASTPRIMEIDX = num + BigInt(2);
        return num;
      }
      num += BigInt(2); // only check odd numbers //
    }
}
Object.prototype.asPrimaryKey=function(){
    var self=this
    var x=(self instanceof Array) ? self : self.split(/\s+/g).Repack() ;
    var y=x.join(' ')
    var N=BigInt(1)
    if(y in PRIMARYKEY){
        N=PRIMARYKEY[y]
    } else {
        x.map((u,i,me)=>{
            var w = !(PRIMARYKEY[u]) ? PRIMARYKEY[u]=u.nextPrime() : PRIMARYKEY[u] ;
            N*=w
        });
        PRIMARYKEY[y]=N
    }
    return N
}
Object.prototype._=function(re,u){
    var self=this
    var s=self.replace(re,u)
    return s
}
Object.prototype.getLHS = function(){
    var self=this;
    
    const indexOfEquals = self.indexOf('=');

    let result=self.splice(0,indexOfEquals);

    return result;
}
Object.prototype.getRHS = function(){
    var self=this;
    
    const indexOfEquals = self.indexOf('=');

    const result=self.splice(indexOfEquals+1);

    return result;
}
Object.prototype.getLHS_String = function(){
    var self=this;
    
    const indexOfEquals = self.indexOf('=');

    const result=self.split(' ').splice(0,indexOfEquals);

    return result.join(' ');
}
Object.prototype.getRHS_String = function(){
    var self=this;
    
    const indexOfEquals = self.indexOf('=');

    const result=self.split(' ').splice(indexOfEquals+1);

    return result.join(' ');
}