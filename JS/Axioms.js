/*

    TITLE:
    Axioms.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.0.16

    DESCRIPTION:
    Main (math) interface to Euclid and its proof components

    UPDATED
    +Auto/Optimal Route performance
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
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
           (u.source in self._lhsCallGraph) &&
            u.indir.match(/Reduce|Auto|Optimal/) &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            var stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            var indir = u.indir
            var flags = u._flags ? u._flags : u.indir ;
            var ProofSUBKEY = u.ProofSUBKEY
            if(
                !(val in self._history._reduce)
            ){
                self._history._reduce[val]=true
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
                ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY) &&
               (ProofSUBKEY = ProofSUBKEY.subkeyUPDATE(self._lhsSUBKEY,self._rhsSUBKEY)) &&
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
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(flags)
                    if(solutionComplete){
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = flags.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = flags.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            solutionEditor.appendlog(s1)
                            solutionEditorR.appendlogR(s2)
                            stackR = []
                            stack = []
                        }
                        solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(!stack.length)
                            solutionEditorR.appendlogR(tmpHTMLR.pre.join(" "))
                        solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        solutionEditorR.appendlogR(P.join(" ")+solutionComplete,"render")
                        imgProgressBar.hide()
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(
                            flags.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:flags,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:flags,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:flags,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                        }
                    }
                } else {
                    clearTimeout(g_code.activeThread)
                    g_code.activeThread=setTimeout(()=>{
                        if(!g_SOLVED){
                            if(stack.length){
                                solutionEditor.appendlog(stack.join('<br><br>'))
                                solutionEditor.appendlog("Prove via % failed."._(/%/,flags))
                                solutionEditorR.appendlogR(stackR.join('<br><br>'),"render")
                                stackR = []
                                stack = []
                            }
                            if(flags.match(/Auto|Optimal/)){
                                solutionEditor.appendlog("<br>========( Reduce )=========<br>========( Expand )=========<br>")
                                reset("partial")
                                console.log("Prove via Reduce failed; now attempting Expand...")
                                postMessage({
                                    source:"axiomROOT",
                                    Proof:g_code.Theorem.lemma,
                                    indir:"Expand",
                                    _flags:flags,
                                    ProofSUBKEY:g_code.Theorem.lemma.asPrimaryKey(),
                                    },g_origin)
                            }
                        } else {
                            e.stopPropagation()
                        }
                        imgProgressBar.hide()
                    },0)
                }
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
           (u.source in self._rhsCallGraph) &&
            u.indir.match(/Expand|Auto|Optimal/) &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            var stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
            var indir = u.indir
            var flags = u._flags ? u._flags : u.indir ;
            var ProofSUBKEY = u.ProofSUBKEY
            if(
                !(val in self._history._expand)
            ){
                self._history._expand[val]=true
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
                ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY) &&
               (ProofSUBKEY = ProofSUBKEY.subkeyUPDATE(self._rhsSUBKEY,self._lhsSUBKEY)) &&
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
                    var P = Proof.collapseEmptyCells()
                    tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete(flags)
                    if(solutionComplete){
                        e.stopPropagation()
                        if(stack.length){
                            var s1 = flags.match(/Optimal/) ? stack.collapseRedundantPaths().join('<br><br>') : stack.join('<br><br>') ;
                            var s2 = flags.match(/Optimal/) ? stackR.collapseRedundantPaths().join('<br>') : stackR.join('<br>') ;
                            solutionEditor.appendlog(s1)
                            solutionEditorR.appendlogR(s2)
                            stackR=[]
                            stack=[]
                        }
                        solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        solutionEditor.appendlog(tmpHTML.post.join(" "))
                        solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        if(!stack.length)
                            solutionEditorR.appendlogR(tmpHTMLR.pre.join(" "))
                        solutionEditorR.appendlogR(P.join(" ")+solutionComplete,"render")
                        imgProgressBar.hide()
                    } else {
                        stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        tmpHTMLR.pre.length && stackR.push( tmpHTMLR.pre.join(" ") )
                        stackR.push( tmpHTMLR.post.join(" ") )
                        if(
                            flags.match(/Auto|Optimal/)
                        ){
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Expand',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:flags,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:'Reduce',
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                _flags:flags,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                        } else {
                            postMessage({
                                source:self._guid,
                                Proof:P,
                                indir:flags,
                                _id:self._id,
                                _stack:stack,
                                _stackR:stackR,
                                ProofSUBKEY:ProofSUBKEY,
                                },g_origin);
                        }
                    }
                } else {
                    clearTimeout(g_code.activeThread)
                    g_code.activeThread=setTimeout(()=>{
                        if(!g_SOLVED){
                            if(stack.length){
                                solutionEditor.appendlog(stack.join('<br><br>'))
                                solutionEditor.appendlog("Prove via % failed."._(/%/,flags))
                                solutionEditorR.appendlogR(stackR.join('<br>'),"render")
                                stackR = []
                                stack = []
                            }
                        } else {
                            e.stopPropagation()
                        }
                        imgProgressBar.hide()
                    },0)
                }
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