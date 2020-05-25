var cblock=`
function workerFunc(e){
    console.info('Hello World!',e.data.msg)
    postMessage({msg:'Complete!'})
}
addEventListener('message',workerFunc)
`
var a=new Worker(URL.createObjectURL(new Blob( [cblock], {type:'text/javascript'} )))
a.onmessage=function(e){ console.info('My worker called!',e.data.msg) }
a.onerror=function(e){ console.info( JSON.stringify(e,' ',2) ) }
a.postMessage({ msg:'Chrome WebWorkers work!' })

function workerFunc(e){
    console.info('Hello World!',e.data.msg)
    postMessage({msg:'Complete!'})
}
var a=new Worker(URL.createObjectURL(new Blob( ['('+(workerFunc.toString())+')()'], {type:'text/javascript'} )))
a.onmessage=function(e){ console.info('My worker called!',e.data.msg) }
a.onerror=function(e){ console.info( JSON.stringify(e,' ',2) ) }
a.postMessage({ msg:'Chrome WebWorkers work!' })


var g_history = {}
  g_history = {}
var g_Solution = []
  g_Solution = []
  
Object.prototype.appendlogR = function(args,bRender){
    var self=this;
    self.textBuffer || (self.textBuffer=[]);
    self.textBuffer.push(args+'<br>')
    if(bRender){
        self.textBuffer && (self.innerHTML=self.textBuffer.join('').replace(/(<br>)+/g,'<br>').split(/<br>/g).join('\n'))
        render({ src:entag(self.innerText),targ:self })
        self.innerHTML+='<br><hr>'
        self.scrollIntoViewIfNeeded()
        self.textBuffer=''
    } else {
    }
}
  if(self.invalidate && self.style.display=='inline'){
      SymbolsViewer(true)
  }
  //addEventListener("message",self._lemmaGovernor)
  
    self._lemmaGovernor = function(e){
        var u = e.data
        if(
            u.source.startsWith('rewrite') &&
            self._guid.startsWith('lemma') &&
            self._isOnline &&
            self._id != u._id &&
            self._lhs &&
            self._rhs &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var ii=(u._id+'p'+self._id)
            if(ii in self._history)
                return
            self._history[ii] = true
            self._subnetFOUND = false
            u._stack = (u._stack && u._stack.length) ? u._stack : [] ;
            var id = u._id
            var from = (u.indir=='Expand') ? self._rhs.split(/\s+/) : self._lhs.split(/\s+/) ;
            var to = (u.indir=='Expand') ? self._lhs.split(/\s+/) : self._rhs.split(/\s+/) ;
            var statement
            var nextStatement
            var COMPOUND = ((self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)) && true)
            if(COMPOUND){
                if(u.indir=='Expand'){
                    statement = (u._lhs+' = '+u._rhs).split(/\s+/)
                    nextStatement = (u._lhs+' = '+u._rhs).split(/\s+/)
                } else /* Auto|Reduce */ {
                    statement = (u._rhs+' = '+u._lhs).split(/\s+/)
                    nextStatement = (u._rhs+' = '+u._lhs).split(/\s+/)
                }
            } else /* SIMPLE */ {
                if(u.indir=='Expand'){
                    statement = u._rhs.split(/\s+/)
                    nextStatement = u._lhs.split(/\s+/)
                } else /* Auto|Reduce */ {
                    statement = u._lhs.split(/\s+/)
                    nextStatement = u._rhs.split(/\s+/)
                }
            }
            var tmp = [];
            var buff = [];
            var intranet = [];
            var vkeys = [];
            // iff SUCCESS //
            var tmpHTML = {
                pre:[...statement],
                post:[...statement],
            }
            var j=0
            var statusCODE;
            // rewrite the axiom //
            statement && statement.map((v,i,me)=>{
                if(v==from[j]) {
                    vkeys.push(i)
                    if(++j==from.length){
                        vkeys.map((idx,k,too)=>{
                            tmpHTML.pre[idx] = me[idx]+self._id.addTAG('sub')
                            tmpHTML.post[idx] = null
                            nextStatement[idx] = null
                            if(k==0){ /* left-associative expressions are DECIDABLE */
                                nextStatement[idx] = to.join(' ')
                                tmpHTML.post[idx] = to.map((w,kk,three)=>{
                                    w+=(ii).addTAG('sub')
                                    return w
                                }).join(' ');
                            }
                        })
                        statusCODE = nextStatement.collapseEmptyCells().join(' ')
                        !self._subnetFOUND && (self._subnetFOUND=true);
                        j=0
                        vkeys = []
                    }
                }
                return v
            })
            if(
                self._subnetFOUND
            ){
                var tmp000 = statusCODE.split(/\s+=\s+/)
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
            }
            // test: axiom <==> basenet //
            if(self._bidirectional) {

            }
        }
    }
      Lemma substitutions rewrite axioms -- which can introduce recursion, stack overflow, and other bugs

      _       _
       |_ = _|     (Reduce)

        _ = _
      _|     |_    (Expand)

      --- = ---    (Exists)
      _
       |_ = _      (Auto)
             |_
                /*
                var obj=g_code[g_GUID]
                postMessage({
                    source:('axiomROOT'),
                    _id:obj._id,
                    _lhs:obj._lhs,
                    _rhs:obj._rhs,
                    _stack:obj._stack,
                    Proof:g_code.Theorem.lemma,
                    indir:u.indir
                    },g_origin)
                */
 //else /* ATTEMPT AXIOM REWRITE */ {
                    postMessage({ 
                        source:self._guid,
                        _id:self._id,
                        _lhs:self._lhs,
                        _rhs:self._rhs,
                        Proof:[...Proof],
                        indir:u.indir,
                        _stack:u._stack 
                    },g_origin)
                //}
                var statement
                var nextStatement
                var COMPOUND_REWRITE = (self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)) && true
                if(COMPOUND_REWRITE){
                    if(u.indir=='Expand'){
                        statement = u._rhs.split(/\s+/)
                        nextStatement = u._lhs.split(/\s+/)
                    } else /* Auto|Reduce */ {
                        statement = u._lhs.split(/\s+/)
                        nextStatement = u._rhs.split(/\s+/)
                    }
                } else /* SIMPLE */ {
                    if(u.indir=='Expand'){
                        statement = u._rhs.split(/\s+/)
                        nextStatement = u._lhs.split(/\s+/)
                    } else /* Auto|Reduce */ {
                        statement = u._lhs.split(/\s+/)
                        nextStatement = u._rhs.split(/\s+/)
                    }
                    statement = (u._lhs+' = '+u._rhs).split(/\s+/)
                    nextStatement = (u._lhs+' = '+u._rhs).split(/\s+/)
                }
  addEventListener("message",self._lemmaGovernor)
    self._lemmaGovernor = function(e){
        var u = e.data
        if(u.source.startsWith("rewrite") && self._guid.startsWith("lemma") && self._id != u._id && self._subnet && self._supernet){
            var val = u.val
            self._subnetFOUND = false
            if(self._isOnline && !(val in g_history) && !(val in self._history) ){
                var id = u._id
                var stream = val.split(/\s+/)
                var from = (u.indir=='Expand') ? self._supernet.split(/\s+/) : self._subnet.split(/\s+/) ;
                var to = (u.indir=='Expand') ? self._subnet.split(/\s+/) : self._supernet.split(/\s+/) ;
                var statement = (u._subnet+' = '+u._supernet).split(/\s+/)
                var nextStatement = (u._subnet+' = '+u._supernet).split(/\s+/)
                var tmp = [];
                var buff = [];
                var intranet = [];
                var vkeys = [];
                // iff SUCCESS //
                var tmpHTML = {
                    pre:[...statement],
                    post:[...statement],
                }
                var j=0
                // rewrite the axiom //
                statement && statement.map((v,i,me)=>{
                    if(v==from[j]) {
                        vkeys.push(i)
                        if(++j==from.length){
                            vkeys.map((idx,k,too)=>{
                                tmpHTML.pre[idx] = me[idx]+self._id.addTAG('sub')
                                tmpHTML.post[idx] = null
                                nextStatement[idx] = null
                                if(k==0){ /* left-associative expressions are DECIDABLE */
                                    nextStatement[idx] = to.join(' ')
                                    tmpHTML.post[idx] = to.map((w,kk,three)=>{
                                        w+=self._id.addTAG('sub')
                                        return w
                                    }).join(' ');
                                }
                            })
                            var statusCODE = nextStatement.join(' ').stripWhiteSpace()
                            if(statusCODE in g_history){
                                return
                            } else {
                                g_history[statusCODE] = true
                                !self._subnetFOUND && (self._subnetFOUND=true);
                            }
                            j=0
                            vkeys = []
                        }
                    }
                    return v
                })
                // try a novel proofstep with the axiom //
                if(self._subnetFOUND && !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                    var tmp000 = nextStatement.join(' ').stripWhiteSpace().split(/\s+=\s+/)
                    var rhs = (tmp000.length>1) ? "" : u._supernet;
                    //self._solutionEditor.appendlog(tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    //self._solutionEditor.appendlog(tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    self._stack.push(
                        tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>',
                        tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    var w = []
                    if(tmp000.length>1){
                        w = (tmp000[0].length>tmp000[1].length) ? [tmp000[0],tmp000[1]] : [tmp000[1],tmp000[0]] ;
                    } else {
                        w = (tmp000[0].length>u._supernet.length) ? [tmp000[0],u._supernet] : [u._supernet,tmp000[0]] ;
                    }
                    var guid = g_code.push(new _AXIOM_
                        ({
                            _guid:"axiom_"+g_GUID++,
                            _id:id,
                            _subnet:w[0],
                            _supernet:w[1],
                            _bidirectional:self._bidirectional,
                            _stack:[...self._stack],
                            _history:{},
                            _isOnline:true,
                            _false:"68934A3E9455FA72420237EB05902327",
                            _basenetFOUND:"68934A3E9455FA72420237EB05902327",
                            _solutionEditor:g_code.solutionEditor
                        })
                    );
                    postMessage({ source:('axiom_rewrite'+guid),val:val,indir:u.indir },g_origin)
                }
                // test: axiom <==> basenet //
                if(self._bidirectional) {

                }
            }
        }
    }
Object.prototype.compileLemmas = function(u,idx){
    var self = this;
    //var basenet_axiom = (u.match(/\s<==/) && true)
    var axiom_any = (u.match(/<==>/) && true)
    //var _u = (basenet_axiom) ? u.split(/\s+<==[>]?\s+/) : u.split(/\s+==>\s+/) ;
    var _u = u.split(/\s+<?==>?\s+/)
    var w = (_u[0].length > _u[1].length) ? [_u[0],_u[1]] : [_u[1],_u[0]] ;
    if(idx in self){
        self[idx]._update
        ({
            _axiom:w[0],
            _basenet:w[1],
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
            _axiom:w[0],
            _basenet:w[1],
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
    if(idx in self){
        self[idx]._update
        ({
            _axiom:(basenet_axiom) ?_u[1]/*.deepSplit()*/ : _u[0]/*.deepSplit()*/,
            _basenet:(basenet_axiom) ?_u[0]/*.deepSplit()*/ : _u[1]/*.deepSplit()*/,
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
            _axiom:(basenet_axiom) ?_u[1]/*.deepSplit()*/ : _u[0]/*.deepSplit()*/,
            _basenet:(basenet_axiom) ?_u[0]/*.deepSplit()*/ : _u[1]/*.deepSplit()*/,
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
                /*
                var rewrite = `axiom_${ id }:lemma_${ self._id } ==> ${ (u._axiom+' = '+u._basenet) }`
                if(rewrite in g_history)
                    return                
                g_history[rewrite] = true
                */
statement && statement.map((v,i,me)=>{
                    if(v!=from[j]){
                        intranet.push(v)
                    } else if(v==from[j]) {
                        vkeys.push(i)
                        if(++j==from.length){
                            buff=[];
                            if(typeof(to)==="object"){
                                tmp.push(...to)
                            } else {
                                tmp.push(to)
                            }
                            !self._subnetFOUND && (self._subnetFOUND=true);
                            vkeys.map((idx,_,too)=>{
                                tmpHTML.pre[idx] = me[idx]+self._id.addTAG('sub')
                                tmpHTML.post[idx] = null
                                nextStatement[idx] = null
                            })
                            nextStatement[(j-1)] = to.join(' ')
                            tmpHTML.post[(j-1)] = to.map((w,k,too)=>{
                                w+=self._id.addTAG('sub')
                                return w
                            }).join(' ');
                            j=0
                            vkeys = []
                        } else {
                            buff.push(v)
                        }
                    }
                    return v
                })
                    /*
                    if(buff.length){
                        tmp.push(buff.join(' '))
                        buff=[];
                    }
                    intranet.unshift(...tmp)
                    var tmp000 = intranet.join(' ').split(/\s+=\s+/)
                    */
SYMP: postMessage not received by _AXIOM_
SOLU:                    