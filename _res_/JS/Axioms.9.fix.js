/*

  TITLE:
    Axioms.js

  AUTHOR: Seagat2011
      http://eterna.cmu.edu/web/player/90270/
      http://fold.it/port/user/1992490

  VERSION:
    Major.Minor.Release.Build
    1.0.0.0

  DESCRIPTION:
    Main (math) operations interface to euclid and its components

  UPDATED
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
    self._auto = function(e){
    }
    self._balance = function(e){
    }
    self._reduce_stepwise = function(){
    }
    self._expand_stepwise = function(){
    }
    self._reduce = function(e){
        var u = e.data
        if(
            u.source.startsWith('axiom') &&
            self._guid.startsWith('axiom') &&
            self._isOnline &&
            self._lhs &&
            self._rhs &&
           (u.source != self._guid) &&
            u.indir.match(/Reduce|Auto/)  &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var ProofFailed = false
            stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            if(
                !(val in g_history) &&
                !(val in self._history)
            ){
                var tmp = []
                var Proof = []
                var vkeys = []
                var from = []
                var to = []
                var tmpHTML = {
                    pre:[],
                    post:[],
                }
                var COMPOUND = Boolean(u._flags && u._flags.match(/Lemma/))
                if(COMPOUND){
                    var stream = (u._lhs+' = '+u._rhs).split(/\s+/)
                    tmp = [...stream]
                    Proof = [...stream]
                    tmpHTML.pre = [...stream]
                    tmpHTML.post = [...stream]
                } else {
                    from = self._lhs.split(/\s+/)
                    to = self._rhs.split(/\s+/)
                    tmp = [...u.Proof]
                    Proof = [...u.Proof]
                    tmpHTML.pre = [...u.Proof]
                    tmpHTML.post = [...u.Proof]
                }
                var jdx = 0
                tmp.map((tok,idx,me=>){
                    if((tok == "=") && (!COMPOUND)){
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
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
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
                    self._history[val] = true
                    g_history[val] = true // comment-out to view other partial-solutions //
                    if(COMPOUND){
                        var ii=(u._id+'p'+self._id)
                        var tmp000 = P.join(' ').split(/\s+=\s+/)
                        var rhs = (tmp000.length>1) ? "" : u._rhs;
                        self._stack.push(
                            tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>',
                            tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                        var w = []
                        if(tmp000.length>1){
                            w = (tmp000[0].length>tmp000[1].length) ? [tmp000[0],tmp000[1]] : [tmp000[1],tmp000[0]] ;
                        } else {
                            w = (tmp000[0].length>u._rhs.length) ? [tmp000[0],u._rhs] : [u._rhs,tmp000[0]] ;
                        }
                        g_code.push(new _AXIOM_
                            ({
                                _guid:'axiom_'+ii,
                                _id:g_GUID,
                                _lhs:w[0],
                                _rhs:w[1],
                                _bidirectional:false,
                                _stack:[...self._stack],
                                _history:{},
                                _isOnline:true,
                                _false:"68934A3E9455FA72420237EB05902327",
                                _basenetFOUND:"68934A3E9455FA72420237EB05902327",
                                _solutionEditor:g_code.solutionEditor
                            })
                        );
                        var obj=g_code[g_GUID]
                        // try a new proofstep using the axiom //
                        postMessage({
                            source:"axiomROOT",
                            Proof:g_code.Theorem.lemma,
                            _stack:obj._stack,
                            indir:u.indir
                            },g_origin)
                        g_GUID++
                        console.log("Axiom_",u._id,"+ Lemma_",`${self._id} (Axiom rewrite performed) => Axiom_${ ii }`)
                    } else {
                        var solutionComplete = P.solutionComplete("Reduce")
                        if(solutionComplete){
                            if(stack.length){
                                self._solutionEditor.appendlog(stack.join('<br><br>'))
                                stack = []
                            }
                            self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                            self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                            self._solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        } else {
                            stack.push(
                                tmpHTML.pre.join(" "),
                                tmpHTML.post.join(" "))
                            postMessage({
                                source:self._guid,
                                _id:self._id,
                                _lhs:self._lhs,
                                _rhs:self._rhs,
                                Proof:P,
                                indir:u.indir,
                                _stack:stack
                                },g_origin);
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<[^>]+>/g,'')}`)
                    }
                }
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
                            stack = []
                        } else {
                            self._solutionEditor.appendlog('*** Reduce failed ***<br><br>')
                        }
                        if(u.indir=='Auto'){
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
            self._guid.startsWith('axiom') &&
            self._isOnline &&
            self._lhs &&
            self._rhs &&
           (u.source != self._guid) &&
            u.indir.match(/Expand/) &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            stack = (u._stack && u._stack.length) ? [...u._stack] : [] ;
            if(
                !(val in g_history) &&
                !(val in self._history)
            ){
                var tmp = []
                var Proof = []
                var vkeys = []
                var from = []
                var to = []
                var tmpHTML = {
                    pre:[],
                    post:[],
                }
                var COMPOUND = Boolean(u._flags && u._flags.match(/Lemma/))
                if(COMPOUND){
                    var stream = (self._lhs+' = '+self._rhs).split(/\s+/)
                    from = u._rhs
                    to = u._lhs
                    tmp = [...stream]
                    Proof = [...stream]
                    tmpHTML.pre = [...stream]
                    tmpHTML.post = [...stream]
                } else {
                    from = self._rhs.split(/\s+/)
                    to = self._lhs.split(/\s+/)
                    tmp = [...u.Proof]
                    Proof = [...u.Proof]
                    tmpHTML.pre = [...u.Proof]
                    tmpHTML.post = [...u.Proof]
                }
                var jdx = 0
                tmp.map((tok,idx,me)=>{
                    if((tok == "=") && (!COMPOUND)){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            self._subnetFOUND = true
                            vkeys.map((kdx,ii)=>{
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map((atok)=>{ return (atok + self._id.addTAG("sub")) }).join(" ")
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
                    self._history[val] = true
                    g_history[val] = true // comment-out to view other partial-solutions //
                    if(COMPOUND){
                        var ii=(u._id+'p'+self._id)
                        var tmp000 = P.join(' ').split(/\s+=\s+/)
                        var rhs = (tmp000.length>1) ? "" : u._rhs;
                        self._stack.push(
                            tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>',
                            tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                        var w = []
                        if(tmp000.length>1){
                            w = (tmp000[0].length>tmp000[1].length) ? [tmp000[0],tmp000[1]] : [tmp000[1],tmp000[0]] ;
                        } else {
                            w = (tmp000[0].length>u._rhs.length) ? [tmp000[0],u._rhs] : [u._rhs,tmp000[0]] ;
                        }
                        g_code.push(new _AXIOM_
                            ({
                                _guid:'axiom_'+ii,
                                _id:g_GUID,
                                _lhs:w[0],
                                _rhs:w[1],
                                _bidirectional:false,
                                _stack:[...self._stack],
                                _history:{},
                                _isOnline:true,
                                _false:"68934A3E9455FA72420237EB05902327",
                                _basenetFOUND:"68934A3E9455FA72420237EB05902327",
                                _solutionEditor:g_code.solutionEditor
                            })
                        );
                        var obj=g_code[g_GUID]
                        // try a new proofstep using the axiom //
                        postMessage({
                            source:"axiomROOT",
                            Proof:g_code.Theorem.lemma,
                            _stack:obj._stack,
                            indir:u.indir
                            },g_origin)
                        g_GUID++
                        console.log("Axiom_",u._id,"+ Lemma_",`${self._id} (Axiom rewrite performed) => Axiom_${ ii }`)
                    } else {
                        var solutionComplete = P.solutionComplete("Expand")
                        if(solutionComplete){
                            if(stack.length){
                                self._solutionEditor.appendlog(stack.join('<br><br>'))
                                stack=[]
                            }
                            self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                            self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                            self._solutionEditor.appendlog(P.join(" ")+solutionComplete)
                        } else {
                            stack.push(
                                tmpHTML.pre.join(" "),
                                tmpHTML.post.join(" "))
                            postMessage({
                                source:self._guid,
                                _id:self._id,
                                _lhs:self._lhs,
                                _rhs:self._rhs,
                                Proof:P,
                                indir:u.indir,
                                _stack:stack
                                },g_origin);
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<[^>]+>/g,'')}`)
                    }
                }
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        if(stack.length){
                            self._solutionEditor.appendlog(stack.join('<br><br>'))
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
                    //i++
                    ltok = lhs[li+i]
                    rtok = rhs[ri+i]
                }
            } else {
                sat = false
            }
        } // test(etok) //
        return sat
    }
  //addEventListener("message",self._auto)
  //addEventListener("message",self._balance)
  addEventListener("message",self._reduce)
  addEventListener("message",self._expand)
}