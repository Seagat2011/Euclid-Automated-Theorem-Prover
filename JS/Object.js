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
    if(
        self.visible
    ){
        if(self.visible!='inline'){ /* fast */
            self.visible='inline'
            self.style.display = 'inline'
        }
    } else if (self.style.display != 'inline'){
        self.visible = 'inline'
        self.style.display = 'inline'
    } else {
        self.visible = 'none'
    }
}
Object.prototype.hide=function(){
    var self=this
    if(
        self.visible
    ){
        if(self.visible!='none'){ /* fast */
            self.visible='none'
            self.style.display = 'none'
        }
    } else if (self.style.display != 'none'){
        self.visible = 'none'
        self.style.display = 'none'
    } else {
        self.visible = 'inline'
    }
}
Object.prototype.appendlogR = function(args,bRender){
    var self=this;
    self.textBuffer || (self.textBuffer=[]);
    args && self.textBuffer.push(...args.split(/<br>|<hr>/g).filter((u)=>{ return u!='' }))
    if(bRender){
        self.textBuffer && render({ src:entag(self.textBuffer.join('\n')),targ:self })
        self.innerHTML+='<br><hr>'
        self.scrollIntoViewIfNeeded()
        self.textBuffer=''
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
  self.scrollIntoViewIfNeeded()
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
Object.prototype.clonePROPS = function(){
    var self=this
    var args={}
    for(var w of arguments){
        args[w]=self[w]
    }
    return args
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
            g_SOLVED = result = "<br><br>Q.E.D. (via "+u+")<br><hr>"
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
  var self = this
  self.Libraries = self.lib.innerText.getLines()
  var s = self.axm.innerText.split(/\n.*Prove[\s\t:]*/)
  self.compileAtomics(s[0].getLines())
  var w
  var lemma
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
  self._init = true
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
    var axiom_any = Boolean(u.match(/<==>/))
    var _u = u.split(/\s+<?==>?\s+/)
    var w = (_u[0].length < _u[1].length) ? [_u[0],_u[1]] : [_u[1],_u[0]] ;
    var guid=self.length
    self.push(new _AXIOM_
    ({
        _guid:"axiom_"+guid,
        _id:guid,
        _rhs:w[0],
        _lhs:w[1],
        _stack:[],
        _history:{ _reduce:{},_expand:{} },
        _rhsSUBKEY:w[0].asPrimaryKey(),
        _lhsSUBKEY:w[1].asPrimaryKey(),
        _isOnline:true,
        _flags:'Lemma',
        _false:"68934A3E9455FA72420237EB05902327",
        _basenetFOUND:"68934A3E9455FA72420237EB05902327",
    })
    );
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
        _history:{ _reduce:{},_expand:{} },
        _isOnline:true,
        _rhsSUBKEY:w[0].asPrimaryKey(),
        _lhsSUBKEY:w[1].asPrimaryKey(),
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
var LASTPRIME=BigInt(2)
var PRIMARYKEY = {}
Object.prototype.nextPrime=function(){
    var u=LASTPRIME
    var Big2=BigInt(2)
    do {
        u++
        var notPrime=false
        var v=BigInt(u/Big2-u%Big2)
        for(var i=v;i>1;i--){
            if (u%i==0){
                notPrime=true
                break
            }
        }
    } while(notPrime);
    LASTPRIME=u
    return u
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
Object.prototype.isaTentativeProof=function(){
    var w=this
    var val=(w/('=').asPrimaryKey())
    var ret=Boolean(Math.sqrt(val.toString())%1==0)
    return ret
}
Object.prototype._=function(re,u){
    var self=this
    var s=self.replace(re,u)
    return s
}
