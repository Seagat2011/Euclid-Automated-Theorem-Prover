/*

  TITLE:
    Axioms.js

  AUTHOR: Seagat2011
      http://eterna.cmu.edu/web/player/90270/
      http://fold.it/port/user/1992490

  VERSION:
    Major.Minor.Release.Build
    0.0.0.17

  DESCRIPTION:
    Main (math) operations interface to euclid and its components

  UPDATED
      +Mulithreaded
      +Auto / Optimal Path functionality
      +Optimal Route
      +Lemmas (Enabled)
      +Scoping functionality

  STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

  REFERENCE:
      Substitution methods:
      1. (direct) AXIOMATIC: 1 + 1 = 2
      2. (indirect) LEMMA SUBSTITUTION: 1 <== 1/1
      Lemma substitutions rewrite axioms -- which can introduce recursion, stack overflow, and other bugs

  SCRIPT TYPE:
    Euclid Tool

*/

function _AXIOM_(){
    var self = this
    var args = arguments[0]
    args.forEach((u)=>{
        self[u] = args[u]
    })
    self._criteria=[[,],[,]] // callback array of [ORs[ANDs,...],[ANDs,...]...] for Axioms (Turing Complete) //
    self._update = function(){
        var args = arguments[0]
        args.forEach((w)=>{
            self[w] = args[w]
            return w
        })
    }
    self._stepREDUCE = function(){
    }
    self._stepEXPAND = function(){
    }
    self._reduce = function(e){
        var u = e.data
        if(
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
            u.indir.match(/Reduce|Auto|Optimal/) &&
           !self._solutionEditor.innerText.match(/Q\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var ProofFailed = false
            var stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            var stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            if(
                !(val in self._history)
            ){
                var tmp = [...u.Proof]
                var Proof = [...u.Proof]
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof] }
                var tmpHTMLR = {
                    pre:[],
                    post:[...u.Proof] }
                if(stackR.length==0)
                    tmpHTMLR.pre=[...u.Proof]
                var from = self._lhs.split(/\s+/)
                var to = self._rhs.split(/\s+/)
                var jdx = 0
                var COMPOUND = Boolean(
                    self._flags &&
                    self._flags.match(/Lemma/) &&
                    (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)))
                tmp.map((tok,idx,me)=>{
                    if((tok == "=") && !COMPOUND){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            g_code._passRound()
                            self._subnetFOUND = true
                            vkeys.map((kdx,ii)=>{
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                tmpHTMLR.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    tmpHTMLR.post[kdx] = to.join(" ")
                                    Proof[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    u._flags && (u.indir=u._flags)
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(u.indir)
                    self._history[val] = true
                    if(solutionComplete){
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = u.indir.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = u.indir.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            self._solutionEditor.appendlog(s1)
                            self._solutionEditorR.appendlogR(s2)
                            stackR = []
                            stack = []
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(!stack.length)
                            self._solutionEditorR.appendlogR(tmpHTMLR.pre.join(" "))
                        self._solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        self._solutionEditorR.appendlogR(P.join(" ")+solutionComplete,"render")
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(
                           (u._flags && u._flags.match(/Auto|Optimal/)) ||
                            u.indir.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                },g_origin);
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                },g_origin);
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:u.indir,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                },g_origin);
                        }
                    }
                    console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<[^>]+>/g,'')}`)
                }
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/Q\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
                            self._solutionEditorR.appendlogR(stackR.join('<br><br>'),"render")
                            stackR = []
                            stack = []
                        }
                        if(u.indir.match(/Auto|Optimal/)){
                            g_code._resetRound()
                            self._solutionEditor.appendlog("<br>========( Reduce )=========<br>========( Expand )=========<br>")
                            reset("partial")
                            console.log("Prove via Reduce failed; now attempting Expand...")
                            postMessage({
                                source:"axiomROOT",
                                Proof:g_code.Theorem.lemma,
                                indir:"Expand"
                                },g_origin)
                        }
                    }
                },0)
            }
        }
    }
    self._expand = function(e){
        var u = e.data
        if(
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
            u.indir.match(/Expand|Auto|Optimal/) &&
           !self._solutionEditor.innerText.match(/Q\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            if(
                !(val in self._history)
            ){
                var tmp = [...u.Proof]
                var Proof = [...u.Proof]
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof]
                }
                var tmpHTMLR = {
                    pre:[],
                    post:[...u.Proof] }
                if(stackR.length==0)
                    tmpHTMLR.pre=[...u.Proof]
                var from = self._rhs.split(/\s+/)
                var to = self._lhs.split(/\s+/)
                var jdx = 0
                var COMPOUND = Boolean(
                    self._flags &&
                    self._flags.match(/Lemma/) &&
                    (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)))
                tmp.map((tok,idx,me)=>{
                    if((tok == "=") && !COMPOUND){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            self._subnetFOUND = true
                            vkeys.map((kdx,ii)=>{
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                tmpHTMLR.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    tmpHTMLR.post[kdx] = to.join(' ')
                                    Proof[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    u._flags && (u.indir=u._flags)
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(u.indir)
                    self._history[val] = true
                    if(solutionComplete){
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = u.indir.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = u.indir.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            self._solutionEditor.appendlog(s1)
                            self._solutionEditorR.appendlogR(s2)
                            stackR=[]
                            stack=[]
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        self._solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        if(!stack.length)
                            self._solutionEditorR.appendlogR(tmpHTMLR.pre.join(" "))
                        self._solutionEditorR.appendlogR(P.join(" ")+solutionComplete,"render")
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(

                           (u._flags && u._flags.match(/Auto|Optimal/)) ||
                            u.indir.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                },g_origin);
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                },g_origin);
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:u.indir,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                },g_origin);
                        }
                    }
                    console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<[^>]+>/g,'')}`)
                }
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/Q\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
                            self._solutionEditorR.appendlogR(stackR.join('<br>'),"render")
                            stackR = []
                            stack = []
                        }
                        g_code._resetRound()
                        reset("partial")
                        console.log("Prove via Expand failed - EXIT 0")
                    }
                },0)
            }
        }
    }
    self._scope_satisfied = function(etok,lhs,li,rhs,ri){
        var i = 1
        var end_scope = { "(":")", "{":"}" }
        var sat = true
        if(lhs[li] != rhs[ri]){
            sat = false
        } else if(etok in end_scope) {
            if(((li+i) in lhs) && ((ri+i) in rhs)){
                var ltok = lhs[li+i]
                var rtok = rhs[ri+i]
                var I = rhs.length // Math.min(lhs.length,rhs.length) //
                etok = end_scope[etok]
                while(i++<I){
                    if(ltok!=rtok){
                        sat = false
                        break
                    }
                    if(rtok == etok){
                        break
                    }
                    ltok = lhs[li+i]
                    rtok = rhs[ri+i]
                }
            } else {
                sat = false
            }
        } // test(etok) //
        return sat
    }
  //addEventListener("message",self._reduce)
  //addEventListener("message",self._expand)
}
var cblock=`
Object.prototype.startsWith = function(re){
  return this.toString().match(new RegExp("^"+re))
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
Object.prototype.stripWhiteSpace = function(){
  return this.replace(/^\s+|\s+$/,"").replace(/\s+/g," ")
}
Object.prototype.addTAG = function(s){
  return "<"+s+">("+this.toString()+")</"+s+">"
}
var axmLIB=[]
function _AXIOM_(){
    var self = this
    var args = arguments[0]
    args.forEach((u)=>{
        self[u] = args[u]
    })
    self._criteria=[[,],[,]] // callback array of [ORs[ANDs,...],[ANDs,...]...] for Axioms (Turing Complete) //
    self._update = function(){
        var args = arguments[0]
        args.forEach((w)=>{
            self[w] = args[w]
            return w
        })
    }
    self._stepREDUCE = function(){
    }
    self._stepEXPAND = function(){
    }
    self._reduce = function(e){
        var u = e.data
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
            u.indir.match(/Reduce|Auto|Optimal/) &&
           !self._solutionEditor.innerText.match(/Q\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var ProofFailed = false
            var stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            var stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            if(
                !(val in self._history)
            ){
                var tmp = [...u.Proof]
                var Proof = [...u.Proof]
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof] }
                var tmpHTMLR = {
                    pre:[],
                    post:[...u.Proof] }
                if(stackR.length==0)
                    tmpHTMLR.pre=[...u.Proof]
                var from = self._lhs.split(/\s+/)
                var to = self._rhs.split(/\s+/)
                var jdx = 0
                var COMPOUND = Boolean(
                    self._flags &&
                    self._flags.match(/Lemma/) &&
                    (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)))
                tmp.map((tok,idx,me)=>{
                    if((tok == "=") && !COMPOUND){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            //g_code._passRound()
                            self._subnetFOUND = true
                            vkeys.map((kdx,ii)=>{
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                tmpHTMLR.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    tmpHTMLR.post[kdx] = to.join(" ")
                                    Proof[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    u._flags && (u.indir=u._flags)
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(u.indir)
                    self._history[val] = true
                    if(solutionComplete){
                        var SOLVED={ txt:[],txtR:[] };
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = u.indir.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = u.indir.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            SOLVED.txt.push(s1)
                            SOLVED.txtR.push(s2)
                            stackR = []
                            stack = []
                        }
                        SOLVED.txt.push(tmpHTML.pre.join(" "))
                        SOLVED.txt.push(tmpHTML.post.join(" "))
                        if(!stack.length)
                            SOLVED.txtR.push(tmpHTMLR.pre.join(" "))
                        SOLVED.txt.push(P.join(" ")+solutionComplete)
                        SOLVED.txtR.push(P.join(" ")+solutionComplete,"render")
                        postMessage({ _solved:true,_stack:SOLVED })
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(
                           (u._flags && u._flags.match(/Auto|Optimal/)) ||
                            u.indir.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                });
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                });
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:u.indir,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                });
                        }
                    }
                    console.log("Source:",u.source,"; target:",self._guid+" (Partial Solution Found) "+solutionComplete.replace(/<[^>]+>/g,''))
                }
            } else {
                clearTimeout(self.activeThread)
                self.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/Q\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
                            self._solutionEditorR.appendlogR(stackR.join('<br><br>'),"render")
                            stackR = []
                            stack = []
                        }
                        if(u.indir.match(/Auto|Optimal/)){
                            //self._resetRound()
                            self._solutionEditor.appendlog("<br>========( Reduce )=========<br>========( Expand )=========<br>")
                            reset("partial")
                            console.log("Prove via Reduce failed; now attempting Expand...")
                            postMessage({
                                source:"axiomROOT",
                                Proof:self.Theorem.lemma,
                                indir:"Expand"
                                })
                        }
                    }
                },0)
            }
        }
    }
    self._expand = function(e){
        var u = e.data
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
            u.indir.match(/Expand|Auto|Optimal/) //&&
           //!self._solutionEditor.innerText.match(/Q\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            if(
                !(val in self._history)
            ){
                var tmp = [...u.Proof]
                var Proof = [...u.Proof]
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof]
                }
                var tmpHTMLR = {
                    pre:[],
                    post:[...u.Proof] }
                if(stackR.length==0)
                    tmpHTMLR.pre=[...u.Proof]
                var from = self._rhs.split(/\s+/)
                var to = self._lhs.split(/\s+/)
                var jdx = 0
                var COMPOUND = Boolean(
                    self._flags &&
                    self._flags.match(/Lemma/) &&
                    (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)))
                tmp.map((tok,idx,me)=>{
                    if((tok == "=") && !COMPOUND){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            self._subnetFOUND = true
                            vkeys.map((kdx,ii)=>{
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                tmpHTMLR.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    tmpHTMLR.post[kdx] = to.join(' ')
                                    Proof[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    u._flags && (u.indir=u._flags)
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(u.indir)
                    self._history[val] = true
                    if(solutionComplete){
                        var SOLVED={ txt:[],txtR:[] };
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = u.indir.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = u.indir.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            SOLVED.txt.push(s1)
                            SOLVED.txtR.push(s2)
                            stackR=[]
                            stack=[]
                        }
                        SOLVED.txt.push(tmpHTML.pre.join(" "))
                        SOLVED.txt.push(tmpHTML.post.join(" "))
                        SOLVED.txt.push(P.join(" ")+solutionComplete)
                        if(!stack.length)
                            SOLVED.txtR.push(tmpHTMLR.pre.join(" "))
                        SOLVED.txtR.push(P.join(" ")+solutionComplete,"render")
                        postMessage({ _solved:true,_stack:SOLVED })
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(
                           (u._flags && u._flags.match(/Auto|Optimal/)) ||
                            u.indir.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                });
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:u.indir,
                                });
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:u.indir,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                });
                        }
                    }
                    console.log("Source:",u.source,"; target:",self._guid+" (Partial Solution Found) "+solutionComplete.replace(/<[^>]+>/g,''))
                }
            } else {
                clearTimeout(self.activeThread)
                self.activeThread=setTimeout(()=>{
                    /*
                    if(!self._solutionEditor.innerText.match(/Q\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
                            self._solutionEditorR.appendlogR(stackR.join('<br>'),"render")
                            stackR = []
                            stack = []
                        }
                        self._resetRound()
                        reset("partial")
                        console.log("Prove via Expand failed - EXIT 0")
                    }
                    */
                    console.log("Prove via Expand failed - EXIT 0")
                },0)
            }
        }
    }
    self._scope_satisfied = function(etok,lhs,li,rhs,ri){
        var i = 1
        var end_scope = { "(":")", "{":"}" }
        var sat = true
        if(lhs[li] != rhs[ri]){
            sat = false
        } else if(etok in end_scope) {
            if(((li+i) in lhs) && ((ri+i) in rhs)){
                var ltok = lhs[li+i]
                var rtok = rhs[ri+i]
                var I = rhs.length // Math.min(lhs.length,rhs.length) //
                etok = end_scope[etok]
                while(i++<I){
                    if(ltok!=rtok){
                        sat = false
                        break
                    }
                    if(rtok == etok){
                        break
                    }
                    ltok = lhs[li+i]
                    rtok = rhs[ri+i]
                }
            } else {
                sat = false
            }
        } // test(etok) //
        return sat
    }
    addEventListener("message",self._reduce)
    addEventListener("message",self._expand)
}
function init(e){
    if(e.data.INIT){
        var b=e.data
        axmLIB=[]
        b.INIT.map((a,i,me)=>{
            var axm=new _AXIOM_( a )
            axmLIB.push( axm )
            return a
        });
        postMessage({
            source:"axiomROOT",
            Proof:b.Proof,
            indir:b.indir,
            })
    }
}
addEventListener('message',init)
`