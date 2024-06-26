/*

    TITLE:
    Axioms.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.4.23

    DESCRIPTION:
    Main (math) interface to Euclid and its proof components

    UPDATED
    +Fixed (Strict) University proofstep bug
    +Temporarily Patched (Strict) University proofstep bug
    -Deprecated experimental deep rewrites (for now)
    +Restrict total rewrites to an upper bound
    -Fixed lhs rewrite bug
    -Fixed postMessage dual postMsg bug
    +Improved stability and responsiveness during proof search
    +Added (Strict) Step-enabled University proofs
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
        const Reduce_Flag = /Reduce/i.test(u.indir);
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
                const shallowRewrite_Flag = (u.source in self._lhsCallGraph);
                const deepRewrite_Flag = Reduce_Flag 
                    && u.ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY)

                if(
                    (shallowRewrite_Flag)
                    || (deepRewrite_Flag)){
                    await self._updateSubkey(u,"Reduce");
                    self._history._reduce[val]=true;
                }
            } // if(!(val in self._history._reduce)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._expand = async function(e){
        const u = e.data;
        const StandardMode_Flag = /Expand|Auto|Optimal/i.test(u.indir);
        const Expand_Flag = /Expand/i.test(u.indir);
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
                const shallowRewrite_Flag = (u.source in self._rhsCallGraph);
                const deepRewrite_Flag = Expand_Flag 
                    && u.ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY);

                if(
                    (shallowRewrite_Flag)
                    || (deepRewrite_Flag)){
                    await self._updateSubkey(u,"Expand");
                    self._history._expand[val]=true;
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
        const fromSubkey = expandingIndir_Flag 
            ? self._rhsSUBKEY 
            : self._lhsSUBKEY ;
        const toSubkey = expandingIndir_Flag
            ? self._lhsSUBKEY
            : self._rhsSUBKEY ;
        (ProofSUBKEY = ProofSUBKEY.subkeyUPDATE(fromSubkey,toSubkey));

        let rewriteCount = false;
        const singleStepRewrite = flags.match(/Step/);

        tmp.map((tok,idx,me)=>{

            if((tok == "=") && !COMPOUND){
                jdx=0;
                vkeys = [];
            }

            if(self._scope_satisfied(tok,me,idx,from,jdx)){
                vkeys.push(idx)
                if(++jdx==from.length){
                    if(singleStepRewrite && rewriteCount){
                        const P_post = tmpHTMLR.post.collapseEmptyCells();
                        
                        // Push rewrites //
                        const QED_phraseR = P_post.join(" ");
                        stack.push( tmpHTML.pre.collapseEmptyCells().join(" ") );
                        stack.push( tmpHTML.post.collapseEmptyCells().join(" ") );
                        stack.push( Proof.collapseEmptyCells().join(" ") );

                        stackR.push(QED_phraseR);
                        // Advance the rewrite step //
                        tmpHTML.post = [...Proof];
                        tmpHTML.pre = [...Proof];
                        // tmpHTML.post; //
                    } else if(singleStepRewrite) {
                        rewriteCount = true;
                        // Push last rewrite //
                        stack.push( Proof.collapseEmptyCells().join(" ") );
                    }
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
        
        const _pre = tmpHTML.pre;
        const _post = tmpHTML.post;
        const _postR = tmpHTMLR.post;

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
                stackR.push( tmpHTMLR.post.join(" ") );

                g_global_message_queue.push({
                        source:self._guid,
                        Proof:P,
                        indir:flags,
                        _id:self._id,
                        _stack:stack,
                        _stackR:stackR,
                        _flags:flags, // Auto|Optimal usually will check this flag //
                        _deepRewritesEnabled_Flag: DeepRewritesEnabled_Flag,
                        ProofSUBKEY:ProofSUBKEY,
                    });
                
                dispatchEvent(dispatchProofstepEvent);
            }
        } else { // self._subnetFOUND == false //
            if(!g_SOLVED){
                solutionEditor.innerHTML = "";
                solutionEditorR.innerHTML = "";
                if(stack.length){
                    solutionEditor.appendlog(stack.join('<br><br>'));
                    solutionEditorR.appendlogR(stackR.join('<br>'));
                }
                solutionEditor.appendlog("Prove via % failed."._(/%/,flags));
                solutionEditorR.appendlogR("Prove via % failed."._(/%/,flags),"render");
                //imgProgressBar.hide();
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
    self._dispatch_message = async function(u){
        if(
            !g_SOLVED 
            && g_global_message_queue.length){
            // Prioritize by length, least to greatest //
            g_global_message_queue.sort((a, b) => { // a > b ?
                const a_lhs = a.Proof.getLHS().length;
                const a_rhs = a.Proof.getRHS().length;
                const b_lhs = b.Proof.getLHS().length;
                const b_rhs = b.Proof.getRHS().length;

                const result = (Math.abs(a_lhs-a_rhs) - Math.abs(b_lhs-b_rhs));

                return result;
            });
            const msg = g_global_message_queue.shift();
            postMessage(msg,g_origin);
        } else if(g_SOLVED){
            g_global_message_queue = [];
        }
    }
    addEventListener("message",self._reduce) // call both Expand|Reduce //
    addEventListener("message",self._expand) // call both Expand|Reduce //
    addEventListener("dispatchProofstep",self._dispatch_message)
}
