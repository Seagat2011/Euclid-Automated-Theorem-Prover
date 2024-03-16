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
            if(
                !(val in self._history._reduce)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._reduce[val]=true;
                self._subnetFOUND = false;
                const subkeyFound_Flag = ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY);
                if(subkeyFound_Flag){
                    self._updateSubkey(u,"Reduce");
                }
            } // if(!(val in self._history._reduce)) //
        } // if(u.source && ... && !g_SOLVED) //
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
            var val = u.Proof.join(' ');
            if(
                !(val in self._history._expand)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._expand[val]=true;
                self._subnetFOUND = false;
                const subkeyFound_Flag = ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY);
                if(subkeyFound_Flag){
                    self._updateSubkey(u,"Expand");
                }
            } // if(!(val in self._history._expand)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._updateSubkey = function(u,indirection){
        const expandingIndir_Flag = /Expand/i.test(indirection);
        var ProofSUBKEY = u.ProofSUBKEY;
        var tmp = [...u.Proof]
        var Proof = [...u.Proof]
        var vkeys = []
        var tmpHTML = {
              pre:[...u.Proof]
            , post:[...u.Proof]
        }
        const from = expandingIndir_Flag
            ? self._rhs.split(/\s+/)
            : self._lhs.split(/\s+/) ;
        const to = expandingIndir_Flag
            ? self._lhs.split(/\s+/)
            : self._rhs.split(/\s+/) ;
        var jdx = 0;
        var stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
        var stackR = (u._stackR && u._stackR.length) ? [...u._stackR] : [] ;
        const indir = u.indir;
        const flags = u._flags ? u._flags : u.indir ;
        var tmpHTMLR = {
              pre:[]
            , post:[...u.Proof] }
        if(stackR.length==0){
            tmpHTMLR.pre=[...u.Proof];
        }
        const COMPOUND = Boolean(
               self._flags
            && self._flags.match(/Lemma/)
            && (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)));
        const removeSubkey = expandingIndir_Flag 
            ? self._rhsSUBKEY 
            : self._lhsSUBKEY ;
        const insertSubkey = expandingIndir_Flag
            ? self._lhsSUBKEY
            : self._rhsSUBKEY ;
        (ProofSUBKEY = ProofSUBKEY.subkeyUPDATE(removeSubkey,insertSubkey)) 
        && tmp.map((tok,idx,me)=>{
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
                imgProgressBar.hide();
                 solutionEditor.innerHTML = ""
                 solutionEditorR.innerHTML = ""
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
             } else { // solutionComplete == false //
                 stack.push(
                      tmpHTML.pre.join(" ")
                    , tmpHTML.post.join(" "))
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
         } else { // self._subnetFOUND == false //
             if(!g_SOLVED){
                 if(stack.length){
                    solutionEditor.innerHTML = "";
                    solutionEditorR.innerHTML = "";

                    solutionEditor.appendlog(stack.join('<br><br>'));
                    solutionEditor.appendlog("Prove via % failed."._(/%/,flags));
                    solutionEditorR.appendlogR(stackR.join('<br>'),"render");
                    imgProgressBar.hide();
                 }
             }
         } // if(self._subnetFOUND) //
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
