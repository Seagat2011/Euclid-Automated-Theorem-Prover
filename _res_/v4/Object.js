/*
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

    REFERENCES

    COMPATIBILITY
        Chrome 53+

*/
Object.prototype.last = function(){
  var i = this.length-1
  return this[i]
}
Object.prototype.mylog = function(){
  var i,I = arguments.length
  var self = this
  this.innerText = ""
  for(i=0;i<I;i++){
    self.innerText += (arguments[i]).toString() + "\n"
  }
}
Object.prototype.clearHTMLWindow=function(){
    var self=this
    self.innerHTML = self.innerText = self.textBuffer=""
}
Object.prototype.showHTMLWindow=function(){
    var self=this
    self.style.display = 'inline'
}
Object.prototype.hideHTMLWindow=function(){
    var self=this
    self.style.display = 'none'
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
            result = "<br><br>Q.E.D. (via "+u+")<br><hr>"
        }
    }
    return result
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
Object.prototype._roundPassed = function(){
  return this._roundStatus
}
Object.prototype._passRound = function(){
  this._roundStatus = true
}
Object.prototype._resetRound = function(){
  this._roundStatus = false
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
        _history:{},
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
        _history:{},
        _isOnline:true,
        _false:"68934A3E9455FA72420237EB05902327",
        _basenetFOUND:"68934A3E9455FA72420237EB05902327",
    })
    );
}
Object.prototype.turnAxiomsOffFrom = function(J){
  var self = this
  var I = self.length
  var j=0
  self.filter((axiom,i,me)=>{
    return (axiom._guid.match(/lemma_/)&&true) || (axiom._guid.match('axiom_') && (++j<=J))
  })
}
Object.prototype.turnLemmasOffFrom = function(J){
  var self = this
  var I = self.length
  var j=0
  self.filter((lemma,i,me)=>{
    return (lemma._guid.match(/axiom_/)&&true) || (lemma._guid.match('lemma_') && (++j<=J))
  })
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