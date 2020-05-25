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
Object.prototype.appendlog = function(){
  var i,I = arguments.length
  var self = this
  for(i=0;i<I;i++){
    self.innerHTML += "<br>" + (arguments[i]).toString() + "<br>"
  }
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
Object.prototype.solutionComplete = function(u){
    var obj = this.join(" ").stripWhiteSpace().split(/\s+=\s+/)
    var result = obj[0]
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
    return result
}
Object.prototype.getLines = function(){
  return this.toString().replace(/^\n*|\n*$/,"").split(/\n/)
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
    lemma:lemma,
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
Object.prototype.compileAtomics = function(a){
    var self = this
    var j=0
    var k=0
    a && a.map((u,i,me)=>{
        if(u.match(/<==|==>/) && true){
            j++
            self.compileLemmas(u.stripWhiteSpace(),i)
        } else {
            k++
            self.compileAxioms(u.stripWhiteSpace(),i)
        }
    });
    self.turnLemmasOffFrom(j)
    self.turnAxiomsOffFrom(k)
}
Object.prototype.compileLemmas = function(u,idx){
    var self = this
    var axiom_any = (u.match(/<==>/) && true)
    var _u = u.split(/\s+<?==>?\s+/)
    var w = (_u[0].length > _u[1].length) ? [_u[0],_u[1]] : [_u[1],_u[0]] ;
    if(idx in self){
        self[idx]._update
        ({
            _subnet:w[0],
            _supernet:w[1],
            _stack:[],
            _history:{},
            _isOnline:true,
            _basenetFOUND:"68934A3E9455FA72420237EB05902327"
        })
    } else {
        self.push(new _AXIOM_
        ({
            _guid:"lemma_"+g_GUID,
            _id:g_GUID,
            _subnet:w[0],
            _supernet:w[1],
            _bidirectional:axiom_any,
            _stack:[],
            _history:{},
            _isOnline:true,
            _false:"68934A3E9455FA72420237EB05902327",
            _basenetFOUND:"68934A3E9455FA72420237EB05902327",
            _solutionEditor:self.solutionEditor
        })
        );
        g_GUID++
    }
}
Object.prototype.compileAxioms = function(u,idx){
    var self = this;
    var _u = u.split(/\s+\=\s+/)
    var w = (_u[0].length > _u[1].length) ? [_u[0],_u[1]] : [_u[1],_u[0]] ;
    if(idx in self){
        self[idx]._update
        ({
            _subnet:_u[0],
            _supernet:_u[1],
            _stack:[],
            _history:{},
            _isOnline:true,
            _basenetFOUND:"68934A3E9455FA72420237EB05902327"
        })
    } else {
        self.push(new _AXIOM_
        ({
            _guid:"axiom_"+g_GUID,
            _id:g_GUID,
            _subnet:_u[0],
            _supernet:_u[1],
            _stack:[],
            _history:{},
            _isOnline:true,
            _false:"68934A3E9455FA72420237EB05902327",
            _basenetFOUND:"68934A3E9455FA72420237EB05902327",
            _solutionEditor:self.solutionEditor
        })
        );
      g_GUID++
    }
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