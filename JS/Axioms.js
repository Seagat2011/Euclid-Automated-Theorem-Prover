/*

    TITLE:
    Axioms.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.0.18

    DESCRIPTION:
    Main (math) interface to Euclid and its proof components

    UPDATED
    +FastForward Support (ie. Proofstep caching) to improve rewrite performance
    +Improved ProofComplete search performance
    +_AXIOM_.optimizeCallGraph
    +Negative proof assertions ~=
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
g_global_rewrite_cache = { 
      _lhs:{}
    , _rhs:{}
};
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
        const u = e.data;
        const StandardMode_Flag = /Reduce|Auto|Optimal/i.test(u.indir);
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
           StandardMode_Flag &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ');
            if(
                !(val in self._history._reduce)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._reduce[val]=true;
               // Likely to converge faster than the following code //
               if((u.source in self._lhsCallGraph)){
                   self._updateSubkey(u,"Reduce");
               }
               if(u.ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY)){
                   self._updateSubkey(u,"Reduce");
               }
            } // if(!(val in self._history._reduce)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._expand = function(e){
        const u = e.data;
        const StandardMode_Flag = /Expand|Auto|Optimal/i.test(u.indir);
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
           StandardMode_Flag &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ');
            if(
                !(val in self._history._expand)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._expand[val]=true;
               // Likely to converge faster than the following code //
                if((u.source in self._rhsCallGraph)){
                    self._updateSubkey(u,"Expand");
                }
                if(u.ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY)){
                     self._updateSubkey(u,"Expand");
                }
            } // if(!(val in self._history._expand)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._updateSubkey = function(u,indirection){
        self._subnetFOUND = false;
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
        (ProofSUBKEY = ProofSUBKEY.subkeyUPDATE(removeSubkey,insertSubkey));

        tmp.map((tok,idx,me)=>{
             if((tok == "=") && !COMPOUND){
                 jdx=0;
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
                     jdx=0;
                     vkeys = [];
                 }
             }
             return tok;
         });

        const currentSUBNET = expandingIndir_Flag
            ? "_lhs"
            : "_rhs" ;
        const oppositeSUBNET = expandingIndir_Flag
            ? "_rhs"
            : "_lhs" ;

        if(!(ProofSUBKEY in g_global_rewrite_cache[currentSUBNET])){
            const _html_pre = expandingIndir_Flag ? tmpHTML.pre.getLHS().join(' ') : tmpHTML.pre.getRHS().join(' ') ;
            const _html_post = expandingIndir_Flag ? tmpHTML.post.getLHS().join(' ') : tmpHTML.post.getRHS().join(' ') ;
            const _proof = expandingIndir_Flag ? Proof.getLHS().join(' ') : Proof.getRHS().join(' ') ;
            const _text = expandingIndir_Flag ? tmpHTMLR.pre.getLHS().join(' ') : tmpHTMLR.pre.getRHS().join(' ') ;

            let tmp_stack = stack.map((s)=>{ return expandingIndir_Flag ? s.getLHS() : s.getRHS() ; });
            let tmp_stackR = stackR.map((s)=>{ return  expandingIndir_Flag ? s.getLHS() : s.getRHS() ; });
            tmp_stack.push(_html_pre);
            tmp_stack.push(_html_post);
            tmp_stack.push(_proof);
            tmp_stackR.push(_text);
            tmp_stackR.push(_proof);

            g_global_rewrite_cache[currentSUBNET][ProofSUBKEY] = { tmp_stack, tmp_stackR };
        }
        if(g_global_rewrite_cache[oppositeSUBNET][ProofSUBKEY]){
            g_SOLVED = true;
            imgProgressBar.hide();
            solutionEditor.innerHTML = "";
            solutionEditorR.innerHTML = "";
            const ret1 = g_global_rewrite_cache._lhs[ProofSUBKEY];
            const ret2 = g_global_rewrite_cache._rhs[ProofSUBKEY];

            const tmp_stack = ret1.tmp_stack;
            const tmp_stackR = ret1.tmp_stackR;
            const tmp_stack_opp = ret2.tmp_stack;
            const tmp_stackR_opp =ret2.tmp_stackR;
            const proofSteps = [];
            const proofStepsR = [];

            const I = Math.max(tmp_stack.length,tmp_stack_opp.length);
            const II = Math.max(tmp_stackR.length,tmp_stackR_opp.length);

            for(let i=0;i<I;++i){
                const _lhs = (i in tmp_stack) ? tmp_stack[i] : tmp_stack.last();
                const _rhs = (i in tmp_stack_opp) ? tmp_stack_opp[i] : tmp_stack_opp.last();
                
                proofSteps.push(`${_lhs} = ${_rhs}`);
            }

            for(let i=0;i<II;++i){
                const _lhs = (i in tmp_stackR) ? tmp_stackR[i] : tmp_stackR.last();
                const _rhs = (i in tmp_stackR_opp) ? tmp_stackR_opp[i] : tmp_stackR_opp.last();
                
                proofStepsR.push(`${_lhs} = ${_rhs}`);
            }

            const s2 = `Q.E.D. (via ${indir} - FastForward)`;

            solutionEditor.appendlog(proofSteps.join('<br>'));
            solutionEditor.appendlog(s2);
            solutionEditorR.appendlogR(proofStepsR.join('<br>'));
            solutionEditorR.appendlogR(s2,"render");
            return;
        }

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
