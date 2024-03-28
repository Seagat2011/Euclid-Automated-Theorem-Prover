/*

    TITLE:
    Axioms.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.0.19

    DESCRIPTION:
    Main (math) interface to Euclid and its proof components

    UPDATED
    +Step enabled proofs
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
    Please note: Lemma substitutions rewrite axioms -- which can introduce recursion, stack overflow, and other bugs

    SCRIPT TYPE:
    Euclid Tool

*/
function _AXIOM_(){
    var self = this
    var args = arguments[0]
    args.forEach((u)=>{
        self[u] = args[u]
    });
    self._lhsCallIDX = 0;
    self._rhsCallIDX = 0;
    self._lhsCallStack = [];
    self._rhsCallStack = [];
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
    self._reduce = async function(e){
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
                if(
                    (u.source in self._lhsCallGraph)
                    && !u._DeepRewritesEnabled_Flag){
                    await self._updateSubkey(u,"Reduce");
                } else if(
                    u._DeepRewritesEnabled_Flag 
                    && u.ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY)){
                    await self._updateSubkey(u,"Reduce");
                }
            } // if(!(val in self._history._reduce)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._expand = async function(e){
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
                if(
                    (u.source in self._rhsCallGraph)
                    && !u._DeepRewritesEnabled_Flag){
                    await self._updateSubkey(u,"Expand");
                } else if(
                    u._DeepRewritesEnabled_Flag 
                    && u.ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY)){
                    await self._updateSubkey(u,"Expand");
                }
            } // if(!(val in self._history._expand)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._updateSubkey = async function(u,indirection){
        self._subnetFOUND = false;
        const expandingIndir_Flag = /Expand/i.test(indirection);
        const DeepRewritesEnabled_Flag = u._DeepRewritesEnabled_Flag;
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
        
        if(flags.match(/Step/)) {
            let idx = 0; // Manually track the index
            let lastFoundIndex = -1; // Track the last index where a token was found, initialize with -1 for none
            for (let tok of tmp) {
                if (tok == "=" && !COMPOUND) {
                    jdx = 0; // Reset on encountering "=" if not in a compound expression
                    lastFoundIndex = -1; // Reset last found index
                }
                if (self._scope_satisfied(tok, tmp, idx, from, jdx)) {
                    // Ensure contiguity by comparing current index with lastFoundIndex (should be consecutive unless it's the first find)
                    if (lastFoundIndex === -1 || lastFoundIndex === idx - 1) {
                        vkeys.push(idx);
                        lastFoundIndex = idx; // Update lastFoundIndex to current
                        if (++jdx == from.length) {
                            self._subnetFOUND = true;
                            for (let [ii, kdx] of vkeys.entries()) { // Use entries() to get both index and value
                                tmpHTML.pre[kdx] += self._id.addTAG("sub");
                                tmpHTML.post[kdx] = null;
                                tmpHTMLR.post[kdx] = null;
                                Proof[kdx] = null;
                                if (ii == 0) {
                                    tmpHTML.post[kdx] = to.map((atok) => atok + self._id.addTAG("sub")).join(" ");
                                    tmpHTMLR.post[kdx] = to.join(' ');
                                    Proof[kdx] = to.join(" ");
                                }
                            }
                            //jdx = 0;
                            //vkeys = [];
                            //lastFoundIndex = -1; // Reset for the next search
                            break;
                        }
                    } else {
                        // Reset if tokens are not contiguous
                        jdx = 0;
                        vkeys = [];
                        lastFoundIndex = -1;
                    }
                }
                idx++; // Manually increment the index
            } // end for (let tok of tmp)

        } else { // Step == false //

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
        }

        const currentSUBNET = expandingIndir_Flag
            ? "_lhs"
            : "_rhs" ;
        const oppositeSUBNET = expandingIndir_Flag
            ? "_rhs"
            : "_lhs" ;
        
        const _pre = tmpHTML.pre;//.collapseEmptyCells();
        const _post = tmpHTML.post;//.collapseEmptyCells();
        const _postR = tmpHTMLR.post;//.collapseEmptyCells();

        const Current_ProofSUBKEY = expandingIndir_Flag ? _pre.getLHS().asPrimaryKey() : _pre.getRHS().asPrimaryKey() ;
        
        const NoCurrentSubnetKeyExists_Flag = !(Current_ProofSUBKEY in g_global_rewrite_cache[currentSUBNET]);
        const OppositeSubnetKeyExists_Flag = (Current_ProofSUBKEY in g_global_rewrite_cache[oppositeSUBNET]);

        if(NoCurrentSubnetKeyExists_Flag){

            const _html_pre = expandingIndir_Flag ? _pre.getLHS_toString() : _pre.getRHS_toString() ;
            const _html_post = expandingIndir_Flag ? _post.getLHS_toString() : _post.getRHS_toString() ;
            const _text = expandingIndir_Flag ? _postR.getLHS_toString() : _postR.getRHS_toString() ;
            const _proof = expandingIndir_Flag ? Proof.getLHS_toString() : Proof.getRHS_toString() ;

            let _stack = stack.map((s)=>{ return expandingIndir_Flag ? s.getLHS_toString() : s.getRHS_toString() ; });
            let _stackR = stackR.map((s)=>{ return  expandingIndir_Flag ? s.getLHS_toString() : s.getRHS_toString() ; });
            
            _stack.push(_html_pre);
            _stack.push(_html_post);
            _stack.push(_proof);
            _stackR.push(_text);

            g_global_rewrite_cache[currentSUBNET][Current_ProofSUBKEY] = { _stack, _stackR };
        }

        const CurrentSubnetKeyExists_Flag = (Current_ProofSUBKEY in g_global_rewrite_cache[currentSUBNET]); // true //

        let ProofFound_Flag = false;

        if(
            CurrentSubnetKeyExists_Flag
            && OppositeSubnetKeyExists_Flag){
            if(
                g_global_rewrite_cache._lhs[Current_ProofSUBKEY]._stack.last()
                == g_global_rewrite_cache._rhs[Current_ProofSUBKEY]._stack.last() ){
                ProofFound_Flag = true;
            }

        }

        if(ProofFound_Flag){
            const ret1 = g_global_rewrite_cache._lhs[Current_ProofSUBKEY];
            const ret2 = g_global_rewrite_cache._rhs[Current_ProofSUBKEY];
            g_SOLVED = true;
            imgProgressBar.hide();
            solutionEditor.innerHTML = "";
            solutionEditorR.innerHTML = "";

            const _stack = ret1._stack;
            const _stackR = ret1._stackR;
            const _stack_opp = ret2._stack;
            const _stackR_opp = ret2._stackR;
            const proofSteps = [];
            const proofStepsR = [];

            const I = Math.max(_stack.length,_stack_opp.length);
            const II = Math.max(_stackR.length,_stackR_opp.length);

            for(let i=0;i<I;++i){
                const _lhs = (i in _stack) ? _stack[i] : _stack.last();
                const _rhs = (i in _stack_opp) ? _stack_opp[i] : _stack_opp.last();
                
                proofSteps.push(`${_lhs} = ${_rhs}`);
            }

            for(let i=0;i<II;++i){
                const _lhs = (i in _stackR) ? _stackR[i] : _stackR.last();
                const _rhs = (i in _stackR_opp) ? _stackR_opp[i] : _stackR_opp.last();
                
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
            tmpHTMLR.post = tmpHTMLR.post.collapseEmptyCells();
            const QED_qualifier = 
                u._DeepRewritesEnabled_Flag 
                && u._DeepRewritesEnabled_Flag == true
                ? " - Deep Rewrite"
                : "" ;
             const solutionComplete = P.solutionComplete(flags,QED_qualifier)
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

                 const QED_phrase = P.join(" ")+solutionComplete;

                 solutionEditor.appendlog(tmpHTML.pre.join(" "))
                 solutionEditor.appendlog(tmpHTML.post.join(" "))
                 solutionEditor.appendlog(QED_phrase)
                 if(!stack.length)
                    solutionEditorR.appendlogR(tmpHTMLR.pre.join(" "))
                 solutionEditorR.appendlogR(QED_phrase,"render")
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
                         _deepRewritesEnabled_Flag: DeepRewritesEnabled_Flag,
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
                         _deepRewritesEnabled_Flag:DeepRewritesEnabled_Flag,
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
