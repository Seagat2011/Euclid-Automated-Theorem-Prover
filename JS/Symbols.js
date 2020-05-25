/*

    TITLE:
        SYMBOLS.js

    AUTHOR: Seagat2011
        http://eterna.cmu.edu/web/player/90270/
        http://fold.it/port/user/1992490

    VERSION:
        Major.Minor.Release.Build
        1.0.0.0

    STYLEGUIDE:
        http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

    REFERENCES:
        N/A

    DESCRIPTION:
        Solve: Given an equation and a set of axioms,
        input as clauses, is there an existing proof
        to link a set of clauses.

        This part of the tool is involved in
        clausal input and equation rendering

    INPUT:
        x plus y equals z

    OUTPUT:
        Pretty-text (Renderer)

    INPUT:
        x = a
        y = b
        a plus b = z
        Prove { x plus y = z }

    OUTPUT:
        Proof found! ..

        x plus y = z              (0000)
        [a] plus y = [a plus b]   (0001)
        a plus y = a plus [y]     (0002)

        done.

    SCRIPT TYPE:
        Euclid Interface / Pretty-text (Renderer)

*/

var FORMULA_FONT_SIZE = 20 // standard font size for formula library //
Array.prototype.Repack = function()
{
   var obj = []
   this.map(function(v,i,me){
      if(v){
         obj.push(v)
      }
      return v
   })
   return obj
}
Object.prototype.Print = function()
{
    return JSON.stringify(this,1,1)
}
Object.prototype.Clone = function(){
    var result
    var status = {
        'object':function(w){
            var o
            if(w instanceof Array){
                o = [];
                w.map(function(v){ o.push(v); return v })
            } else {
                o = {}
                for(var i in w){ if(w.hasOwnProperty(i)){o[i] = w[i]} }
            }
            return o
            },
        'string':function(w){ return w },
        'number':function(w){ return w },
        'default':function(w){ return {} },
    }
    if(status[typeof(this)]){
        result = status[typeof(this)](this)
    } else {
        result = status['default'](this)
    }
    return result
}
var symbolsMAP = {
// Unary / Binary Operators //
'__UBO':'Unary / Binary OPERATORS',
'pos':'+',
'neg':'-',
'plusminus':'&PlusMinus;',
'minusplus':'&MinusPlus;',
'plus':'&plus;',
'minus':'&minus;',
'cdot':"\u22c5",
'times':'&times;', // \u22c5 //
'division':'&div;',
'over':'(1/x)',
'inv':'(1/x)',
'circ':"\u00b0",
'wideslash':'/',
'widebslash':"\\",
'&amp;&amp;':'&and;',
'||':'&or;',
'nor':'&oplus;',
'nand':'&odot;',
'xor':"\u2297",
// RELATIONS (38) //
'__REL':'Relations',
'lessthan':'&lt;',
'greaterthan':'&gt;',
'lessequal':'&le;',
'le':'&le;',
'leslant':'&les;',
'greaterequal':'&ge;',
'geslant':'&ges;',
'muchless':'&ll;',
'muchgreater':'&gg;',
'equals':'&equals;',
'minus':'&minus;',
'noteq':'&ne;',
'approx':'&approx;',
'sim':'&sim;',
'simeq':'&simeq;',
'equiv':"\u2261",
'prop':"\u221d",
'parallel':'&parallel;',
'ortho':"\u22a5",
'divides':"\u2223",
'ndivides':"\u2224",
'toward':"\u2192",
'dlarrow':"\u21d0",
'dlrarrow':"\u21d4",
'drarrow':"\u21d2",
'prec':'&prec;',
'succ':'&succ;',
'preccurlyeq':'&preccurlyeq;',
'succcurlyeq':'&succcurlyeq;',
'precsim':'&precsim;',
'succsim':'&succsim;',
'nprec':'&nprec;',
'nsucc':'&nsucc;',
// SET OPERATIONS (21) //
'__SET':'Set Operations',
'in':'&in;',
'notin':'&notin;',
'owns':"\u220b",
'intersection':'&Intersection;',
'union':'&Union;',
'setminus':'&setminus;',
'slash':'/',
'subset':'&subset;',
'subseteq':'&subseteq;',
'supset':'&supset;',
'supseteq':'&supseteq;',
'nsubset':'&nsubset;',
'nsubseteq':'&nsubseteq;',
'nsupset':'&nsupset;',
'nsupseteq':'&nsupseteq;',
'emptyset':'&emptyset;',
'aleph':'&aleph;',
'setn':"\u2115",
'setz':"\u2124",
'setq':"\u211a",
'setr':"\u211d",
'setc':"\u2102",
'domain':'',
'range':'',
// FUNCTIONS (24) //
'__FNC':'Functions',
'abs':'|',
'fact':'!',
'sqrt':'&Sqrt;',
'nroot':'&Sqrt;',
'func':'f()',
'ln':'',
'exp':'',
'log':'',
'sin':'',
'cos':'',
'tan':'',
'cot':'',
'sec':'',
'csc':'',
'sinh':'',
'cosh':'',
'tanh':'',
'coth':'',
'arcsin':'',
'arccos':'',
'arctan':'',
'arccot':'',
'arsinh':'',
'arcosh':'',
'arctanh':'',
'arcoth':'',
// LEMMA SUBSTITUTION KEYWORDS //LEMMA SUBSTITUTION KEYWORDS
'__LEM':'Lemma Substitutions',
'Digit':'',
'Digits':'',
'Expression':'',
'Expressions':'',
'ID':'',
'Operator':'',
'Statement':'',
'Statements':'',
'Term':'',
'dlarrow ':'\u21d0',
'drarrow ':'\u21d2',
'dlrarrow ':'\u21d4',
// OPERATORS (39) //
'__OPS':'Operators',
'Prove':'',
'lim':'',
'sum':'&sum;',
'prod':'&prod;',
'coprod':'&coprod;',
'int':'&int;',
'iint':'\u222c',
'iiint':'&iiint;',
'lint':'\u222e',
'llint':'\u222f',
'lllint':'\u2230',
'from':'',
'to':'',
'evaluated':'',
'of':'',
'with':'',
'da':'',
'db':'',
'dc':'',
'dd':'',
'de':'',
'df':'',
'dg':'',
'dh':'',
'di':'',
'dj':'',
'dk':'',
'dl':'',
'dm':'',
'dn':'',
'do':'',
'dp':'',
'dq':'',
'dr':'',
'ds':'',
'dt':'',
'du':'',
'dv':'',
'dw':'',
'dx':'',
'dy':'',
'dz':'',
'dtheta':'d&theta;',
'grad':'&nabla;',
'div':'&nabla;\u22c5',
'curl':'&nabla;&times;',
'rad':'',
'degrees':'&deg;',
'minutes':"'",
'seconds':'"',
'ellipses':"\u22ef",
'vellipses':"\u22ee",
'perthousand':"\u2030",
'piecewise':'{',
// JS CONDITIONALS //
'__JSC':'JS Conditionals',
'given':'',
'let':'',
'likewise':'',
'that':'',
'which':'',
'if':'',
'when':'',
'however':'',
'but':'',
'else':'',
'then':'',
'though':'',
'may':'',
'maynot':'',
'must':'',
'mustnot':'',
'isa':'',
'hasa':'',
'and':'',
'or':'',
// ATTRIBUTES (29) //
'__ATT':'Attributes',
'cross':'&times;', //&cross;//
'acute':'&acute;',
'grave':'&grave;',
'breve':'&breve;',
'circle':'\u2218',
'dot':'(text)', // \ue10c //
'ddot':'(text)', // \ue30f //
'dddot':'(text)', // \ue08bt //
'vdddot':'\u22ee',
'bar':'(text)', // \ue30f //
'vec':'&rightarrow;',
'tilde':'&tilde;',
'hat':'&circ;',
'check':'&check;',
'widevec':'&rightarrow;',
'widetilde':'&tilde;',
'widehat':'&circ;',
'overline':'(text)',
'underline':'(text)',
'overstrike':'(text)',
'phantom':'(text)',
'bold':'(text)',
'ital':'(text)',
'size':'(text)',
'font':'(text)',
'color':'(text)',
'black':'(text)',
'blue':'(text)',
'green':'(text)',
'red':'(text)',
'cyan':'(text)',
'magenta':'(text)',
'yellow':'(text)',
// BRACKETS (22) //
'__BRK':'Brackets',
'ldbracket':"\u27e6",
'rdbracket':"\u27e7",
'lbrace':'&lbrace;',
'rbrace':'&rbrace;',
'langle':'&langle;',
'rangle':'&rangle;',
'mline':'',
'lceil':'&lceil;',
'rceil':'&rceil;',
'lfloor':'&lfloor;',
'rfloor':'&rfloor;',
'lline':'|',
'rline':'|',
'ldline':'&parallel;',
'rdline':'&parallel;',
'left':'',
'right':'',
'overbrace':'\u23de',
'underbrace':'\u23df',
'{':'(',
'}':')',
// FORMATS (16) //
'__FMT':'Format',
'lsup':'left-superscript',
'lsub':'left-subscript',
'csup':'top-subscript', // &csup; //
'csub':'bottom-subscript', // &csub; //
'newline':'',
'nospace':'',
'alignl':'(text)',
'alignc':'(text)',
'alignr':'(text)',
'binom':'',
'stack':'',
'matrix':'',
'^':'',
'raised':'^',
'_':'right-subscript',
// OTHERS (19) //
'__OTH':'Other',
'infinity':'&infin;',
'partial':'&part;',
'nabla':'&nabla;',
'exists':'&exist;',
'notexists':'&nexist;',
'forall':'&forall;',
'hbar':'&hbar;',
'lambdabar':'\u019b',
're':'&Re;',
'im':'&Im;',
'wp':'&wp;',
'leftarrow':'&leftarrow;',
'rightarrow':'&rightarrow;',
'uparrow':'&uparrow;',
'downarrow':'&downarrow;',
'dotslow':'\u2026',
'dotsaxis':'\u22ef',
'dotsvert':'\u22ee',
'dotsup':"\u22f0",
'dotsdown':"\u22f1",
'coord':'',
'plane':'',
'field':'',
'surface':'',
'dimension':'',
'manifold':'',
'brane':'',
'coords':'',
'planes':'',
'fields':'',
'surfaces':'',
'dimensions':'',
'manifolds':'',
'branes':'',
// GREEK ALPHABET (23) //
'__GKA':'Greek Alphas',
'alpha':'&alpha;',
'ALPHA':'&Alpha;',
'beta':'&beta;',
'BETA':'&Beta;',
'gamma':'&gamma;',
'GAMMA':'&Gamma;',
'delta':'&delta;',
'DELTA':'&Delta;',
'epsilon':'&epsilon;',
'EPSILON':'&Epsilon;',
'zeta':'&zeta;',
'ZETA':'&Zeta;',
'eta':'&eta;',
'ETA':'&Eta;',
'theta':'&theta;',
'THETA':'&Theta;',
'iota':'&iota;',
'IOTA':'&Iota;',
'kappa':'&kappa;',
'KAPPA':'&Kappa;',
'lambda':'&lambda;',
'LAMBDA':'&Lambda;',
'mu':'&mu;',
'MU':'&Mu;',
'nu':'&nu;',
'NU':'&Nu;',
'xi':'&xi;',
'XI':'&Xi;',
'omicron':'&omicron;',
'OMICRON':'&Omicron;',
'pi':'&pi;',
'PI':'&Pi;',
'rho':'&rho;',
'RHO':'&Rho;',
'sigma':'&sigma;',
'SIGMA':'&Sigma;',
'tau':'&tau;',
'TAU':'&Tau;',
'upsilon':'&upsilon;',
'UPSILON':'&Upsilon;',
'phi':'&phi;',
'PHI':'&Phi;',
'chi':'&chi;',
'CHI':'&Chi;',
'psi':'&psi;',
'PSI':'&Phi;',
'omega':'&omega;',
'OMEGA':'&Omega;',
// GREEK OPERATORS //
'__GKO':'Greek Operators',
'dalpha':'d&alpha;',
'dbeta':'d&beta;',
'dgamma':'d&gamma;',
'ddelta':'d&delta;',
'depsilon':'d&epsilon;',
'dzeta':'d&zeta;',
'deta':'d&eta;',
'dtheta':'d&theta;',
'diota':'d&iota;',
'dkappa':'d&kappa;',
'dlambda':'d&lambda;',
'dmu':'d&mu;',
'dnu':'d&nu;',
'dxi':'d&xi;',
'domicron':'d&omicron;',
'dpi':'d&pi;',
'drho':'d&rho;',
'dsigma':'d&sigma;',
'dtau':'d&tau;',
'dupsilon':'d&upsilon;',
'dphi':'d&phi;',
'dchi':'d&chi;',
'dpsi':'d&psi;',
'domega':'d&omega;',
}
var tdFormula_LHS = '<td class=cssFormula>'
var tdFormulaOperator_LHS = '<td class=cssFormulaOperator>'
var td_RHS = '</td>'
var sup_LHS = '<sup class=cssSUP>'
var sup_RHS = '</sup>'
var sub_LHS = '<sub class=cssSUP>'
var sub_RHS = '</sub>'
//var spanFormulaOperator_LHS = '<span class=cssFormulaOperator>'
var span_alignl_LHS = '<span style="text-align:left">'
var span_alignc_LHS = '<span style="text-align:center">'
var span_alignr_LHS = '<span style="text-align:right">'
var span_overline_LHS = '<span style="text-decoration: overline">'
var span_phantom_LHS = '<span style="visibility:hidden">'
var span_bold_LHS = '<span style="font-weight:bold">'
var span_italic_LHS = '<span style="font-style:italic">'
var span_size_LHS = '<span style="font-size:'
var span_size_MID = 'px;">'
var span_font_LHS = '<span style="font-family:'
var span_font_MID = '">'
var span_color_LHS = '<span style="color:'
var span_color_MID = '">'
var span_black_LHS = '<span class=cssBLACK>'
var span_blue_LHS = '<span class=cssBLUE>'
var span_green_LHS = '<span class=cssGREEN>'
var span_red_LHS = '<span class=cssRED>'
var span_cyan_LHS = '<span class=cssCYAN>'
var span_magenta_LHS = '<span class=cssMAGENTA>'
var span_yellow_LHS = '<span class=cssYELLOW>'
var span_pos_LHS = '<span class=cssPOS>'
var span_RHS = '</span>'
var div_FormulaOperator_LHS = '<div class=cssFormulaOperator>'
var div_RHS = '</div>'
var underline_LHS = '<u>'
var underline_RHS = '</u>'
var overstrike_LHS = '<strike>'
var overstrike_RHS = '</strike>'
function peekSYMBOLrev()
{
    var me = arguments[0]
    var i = arguments[1]
    var j = arguments[1]
    var parenSTACK = { '{':0,'(':0,'[':0 }
    var status = { '}':'{',')':'(',']':'[' }
    var N = -1
    while(i>N){
        var w = me[i].val
        if(w && w.match(/[\{\(\[]/) && parenSTACK[w]){
            parenSTACK[w]--
            if(!(parenSTACK['{'] || parenSTACK['('] || parenSTACK['['])){
                break
            } else {
                i--
            }
        } else
        if(w && w.match(/[\}\)\]]/) ){
            parenSTACK[status[w]]++
            i--
        } else
        if(/*w &&*/ (parenSTACK['{'] || parenSTACK['('] || parenSTACK['['])){ // NOTE: when going backwards, some array elements will be empty
            i-- //NOP//
        } else {
            break
        }
    }/*
    if(i==j){ // no parens used ? //
        i--
    }*/
    return i
}
function peekSYMBOL()
{
    var me = arguments[0]
    var i = arguments[1]
    var j = arguments[1]
    var parenSTACK = { '{':0,'(':0,'[':0 }
    var status = { '}':'{',')':'(',']':'[' }
    var N = me.length
    while(i<N){
        var w = me[i].val
        if(w && w.match(/[\{\(\[]/)){
            parenSTACK[w]++
            i++
        } else
        if(w && w.match(/[\}\)\]]/) && parenSTACK[status[w]]){
            parenSTACK[status[w]]--
            i++
            if(!(parenSTACK['{'] || parenSTACK['('] || parenSTACK['['])){
                break
            }
        } else
        if(w && (parenSTACK['{'] || parenSTACK['('] || parenSTACK['['])){
            i++ //NOP//
        } else {
            break
        }
    }
    if(i==j){ // no parens used ? //
        i++
    }
    return i
}
function peekSYMBOL_DOMAIN() // ignores peekSYMBOL() matching requirements //
{
    var me = arguments[0]
    var i = arguments[1]
    var j = arguments[1]
    var parenSTACK = 0
    var N = me.length
    while(i<N){
        var w = me[i].val
        if(w && w.match(/[\{\(\[]/)){
            parenSTACK++
            i++
        } else
        if(w && w.match(/[\}\)\]]/) && parenSTACK){
            parenSTACK--
            i++
            if(!parenSTACK){
                break
            }
        } else
        if(w && parenSTACK){
            i++ //NOP//
        } else
        {
            break
        }
    }
    if(i==j){ // no parens used ? //
        i++
    }
    return i
}
function genSCOPE() // Destructive READ //
{
    var v = arguments[0]
    var i = arguments[1]
    var j = arguments[2]
    var s = []
    var pc = j
    v.pc = i
    do{
        var w = v[i].val
        var tmp_pc = i
        s.push(buildSYMBOL[w]?buildSYMBOL[w](v,i):w)
        if(v.pc > tmp_pc){
            i = v.pc-1
        }
        v[i++].val=''
    }while(i<j);
    v.pc = pc
    return s.join(' ')
}
function peekSCOPE() // READ-ONLY (non destructive)
{
    var v = arguments[0]
    var i = arguments[1]
    var j = arguments[2]
    var s = []
    var pc = j
    v.pc = i
    do{
        var w = v[i].val
        var tmp_pc = i
        s.push(buildSYMBOL[w]?buildSYMBOL[w](v,i):w)
        if(v.pc > tmp_pc){
            i = v.pc-1
        }
        i++
    }while(i<j);
    v.pc = pc
    return s.join(' ')
}
function generateBOUNDS()
{
    var v = arguments[0]
    var j = arguments[1]
    var s = arguments[0][ arguments[1] ].val
    var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k);
    var m = v[j].val
    if(m && m.match(/from|to/)){
        var tmp_pc = j
        buildSYMBOL[m](v,j) // tdLOWER .. tdUPPER //
    }
    return s
}
var buildSYMBOL = {
// Unary / Binary Operators
'pos':function(){ return sup_LHS+'+'+sup_RHS },
'neg':function(){ return sup_LHS+'-'+sup_RHS },
'plusminus':function(){ return '&PlusMinus;' },
'minusplus':function(){ return '&MinusPlus;' },
'plus':function(){ return '&plus;' },
'minus':function(){ return '&minus;' },
'cdot':function(){ return "\u22c5" },
'times':function(){ return '&times;'  }, // '\u22c5' //
'division':function(){ return '&div;' },
'over':function(){ return '/' },
'inv':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return '1/'+s },
'circ':function(){ return "\u00b0" },
'wideslash':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var d = peekSCOPE(v,j,k);
    var s = peekSCOPE(v,k,l);
    return '<table><tbody class=cssFormula><tr><td>'+d+'</td><td>'+div_FormulaOperator_LHS+'/'+div_RHS+'</td><td>'+s+'</td></tr></tbody></table>' },
'widebslash':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var d = peekSCOPE(v,j,k);
    var s = peekSCOPE(v,k,l);
    return '<table><tbody class=cssFormula><tr><td>'+d+'</td><td>'+div_FormulaOperator_LHS+'\\'+div_RHS+'</td><td>'+s+'</td></tr></tbody></table>' },
'&&':function(){ return '&and;' },
'\|\|':function(){ return '&or;' },
'nor':function(){ return '&oplus;' },
'nand':function(){ return '&odot;' },
'xor':function(){ return "\u2297" },
// RELATIONS (38)
'lessthan':function(){ return '&lt;' },
'greaterthan':function(){ return '&gt;' },
'lessequal':function(){ return '&le;' },
'le':function(){ return '&le;' },
'leslant':function(){ return '&les;' },
'greaterequal':function(){ return '&ge;' },
'geslant':function(){ return '&ges;' },
'muchless':function(){ return '&ll;' },
'muchgreater':function(){ return '&gg;' },
'equals':function(){ return '&equals;' },
'minus':function(){ return '&minus;' },
'noteq':function(){ return '&ne;' },
'approx':function(){ return '&approx;' },
'sim':function(){ return '&sim;' },
'simeq':function(){ return '&simeq;' },
'equiv':function(){ return "\u2261" },
'prop':function(){ return "\u221d" },
'parallel':function(){ return '&parallel;' },
'ortho':function(){ return "\u22a5" }, // orthog //
'divides':function(){ return "\u2223" },
'ndivides':function(){ return "\u2224" },
'toward':function(){ return "\u2192" },
'dlarrow':function(){ return "\u21d0" },
'dlrarrow':function(){ return "\u21d4" },
'drarrow':function(){ return "\u21d2" },
'==>':function(){ return "\u21d2" },
'<==':function(){ return "\u21d0" },
'<==>':function(){ return "\u21d4" },
'prec':function(){ return '&prec;' },
'succ':function(){ return '&succ;' },
'preccurlyeq':function(){ return '&preccurlyeq;' },
'succcurlyeq':function(){ return '&succcurlyeq;' },
'precsim':function(){ return '&precsim;' },
'succsim':function(){ return '&succsim;' },
'nprec':function(){ return '&nprec;' },
'nsucc':function(){ return '&nsucc;' },
// SET OPERATIONS (21)
'in':function(){ return '&in;' },
'notin':function(){ return '&notin;' },
'owns':function(){ return "\u220b" },
'intersection':function(){ return '&Intersection;' },
'union':function(){ return '&Union;' },
'setminus':function(){ return '&setminus;' },
'slash':function(){ return '/' },
'subset':function(){ return '&subset;' },
'subseteq':function(){ return '&subseteq;' },
'supset':function(){ return '&supset;' },
'supseteq':function(){ return '&supseteq;' },
'nsubset':function(){ return '&nsubset;' },
'nsubseteq':function(){ return '&nsubseteq;' },
'nsupset':function(){ return '&nsupset;' },
'nsupseteq':function(){ return '&nsupseteq;' },
'emptyset':function(){ return '&emptyset;' },
'aleph':function(){ return '&aleph;' },
'setn':function(){ return "\u2115" },
'setz':function(){ return "\u2124" },
'setq':function(){ return "\u211a" },
'setr':function(){ return "\u211d" },
'setc':function(){ return "\u2102" },
'domain':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var q = peekSCOPE(v,j,k); return ('{'+q+'}') },
'range':function(){ var v = arguments[0]; var j = arguments[1]; var k = ++j;
    var s = []
    if(v[k] && v[k].val.match(/[\{\(\[]/)){
        s.push(v[k++].val);
        while(v[k] && !v[k].val.match(/[\}\)\]]/))
        {
            var n = v[k].val;
            s.push(buildSYMBOL[n]?buildSYMBOL[n](v,k):n);
            k++
        }
        s.push(v[k++].val);
    }
    v.pc = k
    return s.join(' ')
    },
// FUNCTIONS (24)
'abs':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var q = peekSCOPE(v,j,k); return ('|'+q+'|') },
'fact':function(){ var v = arguments[0]; var j = arguments[1]; return '!' },
'sqrt':function(){ return '&Sqrt;' },
'nroot':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var s = peekSCOPE(v,j,k); var q = peekSCOPE(v,k,l); return (sup_LHS+s+sup_RHS+'&Sqrt;'+q) },
'func':function(){ return 'f()' },
'ln':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'exp':function(){ var v = arguments[0]; var j = arguments[1]; return 'e ' },
'log':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'sin':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'cos':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'tan':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'cot':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'sec':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'csc':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'sinh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'cosh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'tanh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'coth':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arcsin':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arccos':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arctan':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arccot':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arsinh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arcosh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arctanh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'arcoth':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
// OPERATORS (39)
'Prove':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return 'Prove : '+s },
'lim':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+v[j].val+div_RHS
    },
'sum':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return (div_FormulaOperator_LHS+'&sum;'+div_RHS)
    },
'prod':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'&prod;'+div_RHS
    },
'coprod':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'&coprod;'+div_RHS
    },
'int':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'&int;'+div_RHS
    },
'iint':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'\u222c'+div_RHS
    },
'iiint':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'&iiint;'+div_RHS
    },
'lint':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'\u222e'+div_RHS
    },
'llint':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'\u222f'+div_RHS
    },
'lllint':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'\u2230'+div_RHS
    },
'evaluated':function(){ var v = arguments[0]; var j = arguments[1]; return this['evaluate'](v,j)},
'evaluate':function(){ var v = arguments[0]; var j = arguments[1];
    generateBOUNDS(v,j)
    return div_FormulaOperator_LHS+'|'+div_RHS
    },
'da':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'db':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dc':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dd':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'de':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'df':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dg':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dh':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'di':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dj':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dk':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dl':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dm':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dn':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'do':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dp':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dq':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dr':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'ds':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dt':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'du':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dv':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dw':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dx':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dy':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dz':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dtheta':function(){ return 'd&theta;' },
'grad':function(){ return '&nabla;' },
'div':function(){ return '&nabla;\u22c5' },
'curl':function(){ return '&nabla;&times;' },
'rad':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'degrees':function(){ return '&deg;' },
'minutes':function(){ return "'" },
'seconds':function(){ return '"' },
'ellipses':function(){ return "\u22ef" },
'vellipses':function(){ return "\u22ee" },
'perthousand':function(){ return "\u2030" },
'piecewise':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL_DOMAIN(v,++j); var s = '';
    if(v[j] && v[j].val.match(/\{/)){
        v.tdTALLY = 0; v.trTALLY = 0;
        var d = '{'+peekSCOPE(v,j,k)+'}';
        var c = (v.trTALLY+2.7)*FORMULA_FONT_SIZE;
        v.tdTALLY = undefined; v.trTALLY = undefined;
        s = '</td>'+d
        .replace(/^(\{)/gm,'<td class=cssPIECEWISE style="font-size:'+c+';">$1</td><td>')
        .replace(/\}$/gm,'</td>')+'<td>'
    }
    return s
    },
// JS CONDITIONALS
'given':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'let':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'likewise':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'that':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'which':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'if':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'when':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'however':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'but':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'else':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'then':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'though':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'may':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'maynot':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'must':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'mustnot':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'isa':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'hasa':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'and':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'or':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'of':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val; var i = peekSYMBOLrev(v,j-1); var x = peekSCOPE(v,i,j); if(x && x.length<2 && !x.match(/\d/)){ var k = peekSYMBOL(v,++j); x = peekSCOPE(v,j,k); s = '( '+x+' )'; } return s },
'from':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    var i = peekSYMBOLrev(v,j-1);
    if(v[i] && v[i].val.match(/sum|i{1,3}nt|l{1,3}int|prod|coprod|lim|evaluated?/)){
        // current scope //
        var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
        v[i].tdLOWER = buildSYMBOL[s]?buildSYMBOL[s](v,j):s;
        // lookahead //
        if(v[k] && v[k].val.match(/^to$/)){
            j = ++k
            k = peekSYMBOL(v,j);
            var n = peekSCOPE(v,j,k);
            v[i].tdUPPER = buildSYMBOL[n]?buildSYMBOL[n](v,j):n;
        }
        s = ''
    }
    return s
    },
'to':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    var i = peekSYMBOLrev(v,j-1);
    var h = peekSYMBOLrev(v,i-1);
    var g = peekSYMBOLrev(v,h-1);
    // LBOUNDS also exists ? //
    if(v[g] && v[g].val.match(/sum|i{1,3}nt|l{1,3}int|prod|coprod|lim|evaluated?/)){
        var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
        v[g].tdUPPER = (buildSYMBOL[s]?buildSYMBOL[s](v,j):s);
        s = ''
    }
    else // UBOUNDS exclusively //
    if(v[i] && v[i].val.match(/sum|i{1,3}nt|l{1,3}int|prod|coprod|lim|evaluated?/)){
        var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
        v[i].tdUPPER = (buildSYMBOL[s]?buildSYMBOL[s](v,j):s);
        s = ''
    }
    return s
    },
'with':function(){ var v = arguments[0]; var j = arguments[1]; return 'with '+v[j].val },
// ATTRIBUTES (29)
'cross':function(){ return '&times;' }, // &cross; //
'acute':function(){ return '&acute;' },
'grave':function(){ return '&grave;' },
'breve':function(){ return '&breve;' },
'circle':function(){ return '\u2218' }, // overhead circle //
'dot':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    v[j].tdUPPER = sub_LHS+'\u22c5'+sub_RHS
    var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
    return s
    }, //' \ue10c' //
'ddot':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    v[j].tdUPPER = sub_LHS+'\u22c5\u22c5'+sub_RHS
    var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
    return s
    }, // ' \ue30f' //
'dddot':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    v[j].tdUPPER = sub_LHS+'\u22c5\u22c5\u22c5'+sub_RHS
    var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
    return s
    }, //' \ue08bt' //
'vdddot':function(){ return '\u22ee' },
'bar':function(){ var v = arguments[0]; var j = arguments[1]; return this['overline'](v,j) }, // '\ue30f'//
'vec':function(){ var v = arguments[0]; var j = arguments[1]; var s = v[j].val;
    v[j].tdUPPER = sub_LHS+'&rightarrow;'+sub_RHS
    var k = peekSYMBOL(v,++j); s = peekSCOPE(v,j,k);
    return s
    },
'tilde':function(){ return '&tilde;' },
'hat':function(){ return '&circ;' },
'check':function(){ return '&check;' },
'widevec':function(){ return '&rightarrow;' },
'widetilde':function(){ return '&tilde;' },
'widehat':function(){ return '&circ;' },
'overline':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_overline_LHS+s+span_RHS) },
'underline':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (underline_LHS+s+underline_RHS) },
'overstrike':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (overstrike_LHS+s+overstrike_RHS) },
'phantom':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_phantom_LHS+s+span_RHS) },
'bold':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_bold_LHS+s.join(' ')+span_RHS) },
'ital':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_italic_LHS+s.join(' ')+span_RHS) },
'size':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = peekSCOPE(v,j,k); var s = peekSCOPE(v,k,l); return (span_size_LHS+d.replace(/[^\d]+/g,'')+span_size_MID+s+span_RHS) },
'font':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = peekSCOPE(v,j,k); var s = peekSCOPE(v,k,l); return (span_font_LHS+d.replace(/[\)\(\{\}\[\]]+/g,'')+span_font_MID+s+span_RHS) },
'color':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = []; do{ d.push(v[j].val); j++;/*v[j++]='';*/ }while(j<k); v.pc = k; d.join(' '); var s = peekSCOPE(v,k,l); return (span_color_LHS+d+span_color_MID+s+span_RHS) },
'black':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_black_LHS+s+span_RHS) },
'blue':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_blue_LHS+s+span_RHS) },
'green':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_green_LHS+s+span_RHS) },
'red':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_red_LHS+s+span_RHS) },
'cyan':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_cyan_LHS+s+span_RHS) },
'magenta':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_magenta_LHS+s+span_RHS) },
'yellow':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (span_yellow_LHS+s+span_RHS) },
// BRACKETS (22)
'ldbracket':function(){ return "\u27e6" },
'rdbracket':function(){ return "\u27e7" },
'lbrace':function(){ return '&lbrace;' },
'rbrace':function(){ return '&rbrace;' },
'langle':function(){ return '&langle;' },
'rangle':function(){ return '&rangle;' },
'mline':function(){ return '' },
'lceil':function(){ return '&lceil;' },
'rceil':function(){ return '&rceil;' },
'lfloor':function(){ return '&lfloor;' },
'rfloor':function(){ return '&rfloor;' },
'lline':function(){ return '|' },
'rline':function(){ return '|' },
'ldline':function(){ return '&parallel;' },
'rdline':function(){ return '&parallel;' },
'left':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = ''; var s = '';
    if(v[j].val.match(/[\[\(\{]/) && v[j+1].val.match(/matrix|binom|stack/)){
        v.tdTALLY = 0; v.trTALLY = 0;
        d = peekSCOPE(v,j,k);
        var c = (v.trTALLY+2)*FORMULA_FONT_SIZE;
        v.tdTALLY = undefined; v.trTALLY = undefined;
        s = d
        .replace(/^([\[\{\(])/gm,'</td><td class=cssMATRIX style="font-size:'+c+';">$1')
        .replace(/<td>\s*([\]\}\)]).*$/gm,'<td class=cssMATRIX style="font-size:'+c+';">$1</td><td>')
    }
    return s
    },
'right':function(){ var v = arguments[0]; var j = arguments[1]; return '' },
'overbrace':function(){ return '\u23de' },
'underbrace':function(){ return '\u23df' },
'{':function(){ return '' }, // '(' //
'}':function(){ return '' }, // ')' //
'(':function(){ return '(' },
')':function(){ return ')' },
'[':function(){ return '[' },
']':function(){ return ']' },
// FORMATS (16)
'lsup':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    v[j-1].tdUPPER = s
    return '&nbsp;&nbsp;&nbsp;&nbsp;'+b
    }, // superscript x (left-sided) //
'lsub':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    v[j-1].tdLOWER = b
    return '&nbsp;&nbsp;&nbsp;&nbsp;'+s
    }, // subscript x (lef-sided) //
'csup':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    v[j-1].tdUPPER = s
    return b
    }, // &csup; stack (overhead) //
'csub':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    v[j-1].tdLOWER = b
    return s
    }, // &csub; stack (underneath) //
'newline':function(){ var v = arguments[0]; var j = arguments[1]; return '<br></br>' },
'nospace':function(){ var v = arguments[0]; var j = arguments[1]; return '' },
'alignl':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = peekSCOPE(v,j,k); var s = peekSCOPE(v,k,l); return (span_alignl_LHS+d.replace(/[\)\(\{\}\[\]]+/g,'')+span_RHS+s) },
'alignc':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = peekSCOPE(v,j,k); var s = peekSCOPE(v,k,l); return (span_alignc_LHS+d.replace(/[\)\(\{\}\[\]]+/g,'')+span_RHS+s) },
'alignr':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var l = peekSYMBOL(v,k); var d = peekSCOPE(v,j,k); var s = peekSCOPE(v,k,l); return (span_alignr_LHS+d.replace(/[\)\(\{\}\[\]]+/g,'')+span_RHS+s) },
'binom':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    if(typeof(v.tdTALLY)=='undefined'){
        v.tdTALLY = 2;
    }
    if(typeof(v.trTALLY)=='undefined'){
        v.trTALLY = 0;
    }
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    var c = (v.trTALLY+0)*FORMULA_FONT_SIZE;
    return ('</td><td class=cssMATRIX style="font-size:'+c+'">(</td><td>'+s+'<br/>'+b+'</td><td class=cssMATRIX style="font-size:'+c+'">)</td><td>')
    },
'stack':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    var l = peekSYMBOL(v,k);
    if(typeof(v.tdTALLY)=='undefined'){
        v.tdTALLY = 2;
    }
    if(typeof(v.trTALLY)=='undefined'){
        v.trTALLY = 0;
    }
    var s = peekSCOPE(v,j,k);
    var b = peekSCOPE(v,k,l);
    return ('</td><td>'+s+'<br/>'+b+'</td><td>')
    },
'matrix':function(){ var v = arguments[0]; var j = arguments[1];
    var k = peekSYMBOL(v,++j);
    if(typeof(v.tdTALLY)=='undefined'){
        v.tdTALLY = 0;
    }
    if(typeof(v.trTALLY)=='undefined'){
        v.trTALLY = 0;
    }
    var s = peekSCOPE(v,j,k);
    return ('</td><td>'+s+'</td><td>')
    },
'#':function(){ var v = arguments[0]; var j = arguments[1]; var d = '#'; if(v.tdTALLY!=undefined){ v.tdTALLY++; d = ' ' } return d },
/* Add #+ as needed */
'##':function(){ var v = arguments[0]; var j = arguments[1]; if(v.trTALLY!=undefined){ v.trTALLY++; v.tdTALLY = 0; } return '<br/>' },
'^':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return sup_LHS+s+sup_RHS },
'raised':function(){ var v = arguments[0]; var j = arguments[1]; return this['^'](v,j) },
'_':function(){ var v = arguments[0]; var j = arguments[1]; var k = peekSYMBOL(v,++j); var s = peekSCOPE(v,j,k); return (sub_LHS+s+sub_RHS) },
// OTHERS (19)
'infinity':function(){ return '&infin;' },
'partial':function(){ return '&part;' },
'nabla':function(){ return '&nabla;' },
'exists':function(){ return '&exist;' },
'notexists':function(){ return '&nexist;' },
'forall':function(){ return '&forall;' },
'hbar':function(){ return '&hbar;' },
'lambdabar':function(){ return '\u019b' },
're':function(){ return '&Re;' },
'im':function(){ return '&Im;' },
'wp':function(){ return '&wp;' },
'leftarrow':function(){ return '&leftarrow;' },
'rightarrow':function(){ return '&rightarrow;' },
'uparrow':function(){ return '&uparrow;' },
'downarrow':function(){ return '&downarrow;' },
'dotslow':function(){ return '\u2026' },
'dotsaxis':function(){ return '\u22ef' },
'dotsvert':function(){ return '\u22ee' },
'dotsup':function(){ return "\u22f0" },
'dotsdown':function(){ return "\u22f1" },
'coord':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'plane':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'field':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'surface':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dimension':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'manifold':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'brane':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'coords':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'planes':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'fields':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'surfaces':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'dimensions':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'manifolds':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
'branes':function(){ var v = arguments[0]; var j = arguments[1]; return v[j].val },
// GREEK ALPHABET (23)
'alpha':function(){ return '&alpha;' },
'ALPHA':function(){ return '&Alpha;' },
'beta':function(){ return '&beta;' },
'BETA':function(){ return '&Beta;' },
'gamma':function(){ return '&gamma;' },
'GAMMA':function(){ return '&Gamma;' },
'delta':function(){ return '&delta;' },
'DELTA':function(){ return '&Delta;' },
'epsilon':function(){ return '&epsilon;' },
'EPSILON':function(){ return '&Epsilon;' },
'zeta':function(){ return '&zeta;' },
'ZETA':function(){ return '&Zeta;' },
'eta':function(){ return '&eta;' },
'ETA':function(){ return '&Eta;' },
'theta':function(){ return '&theta;' },
'THETA':function(){ return '&Theta;' },
'iota':function(){ return '&iota;' },
'IOTA':function(){ return '&Iota;' },
'kappa':function(){ return '&kappa;' },
'KAPPA':function(){ return '&Kappa;' },
'lambda':function(){ return '&lambda;' },
'LAMBDA':function(){ return '&Lambda;' },
'mu':function(){ return '&mu;' },
'MU':function(){ return '&Mu;' },
'nu':function(){ return '&nu;' },
'NU':function(){ return '&Nu;' },
'xi':function(){ return '&xi;' },
'XI':function(){ return '&Xi;' },
'omicron':function(){ return '&omicron;' },
'OMICRON':function(){ return '&Omicron;' },
'pi':function(){ return '&pi;' },
'PI':function(){ return '&Pi;' },
'rho':function(){ return '&rho;' },
'RHO':function(){ return '&Rho;' },
'sigma':function(){ return '&sigma;' },
'SIGMA':function(){ return '&Sigma;' },
'tau':function(){ return '&tau;' },
'TAU':function(){ return '&Tau;' },
'upsilon':function(){ return '&upsilon;' },
'UPSILON':function(){ return '&Upsilon;' },
'phi':function(){ return '&phi;' },
'PHI':function(){ return '&Phi;' },
'chi':function(){ return '&chi;' },
'CHI':function(){ return '&Chi;' },
'psi':function(){ return '&psi;' },
'PSI':function(){ return '&Phi;' },
'omega':function(){ return '&omega;' },
'OMEGA':function(){ return '&Omega;' },
// GREEK OPERATORS
'dalpha':function(){ return 'd&alpha;' },
'dbeta':function(){ return 'd&beta;' },
'dgamma':function(){ return 'd&gamma;' },
'ddelta':function(){ return 'd&delta;' },
'depsilon':function(){ return 'd&epsilon;' },
'dzeta':function(){ return 'd&zeta;' },
'deta':function(){ return 'd&eta;' },
'dtheta':function(){ return 'd&theta;' },
'diota':function(){ return 'd&iota;' },
'dkappa':function(){ return 'd&kappa;' },
'dlambda':function(){ return 'd&lambda;' },
'dmu':function(){ return 'd&mu;' },
'dnu':function(){ return 'd&nu;' },
'dxi':function(){ return 'd&xi;' },
'domicron':function(){ return 'd&omicron;' },
'dpi':function(){ return 'd&pi;' },
'drho':function(){ return 'd&rho;' },
'dsigma':function(){ return 'd&sigma;' },
'dtau':function(){ return 'd&tau;' },
'dupsilon':function(){ return 'd&upsilon;' },
'dphi':function(){ return 'd&phi;' },
'dchi':function(){ return 'd&chi;' },
'dpsi':function(){ return 'd&psi;' },
'domega':function(){ return 'd&omega;' },
'C21F969B5F03D33D43E04F8F136E7682':function(){ v = arguments[0]; j = arguments[1]; var s = v[j].val; if((s && s.match(/\w/) && s.match(/\W/))||(s.match(/\{|\}/))){ s = span_red_LHS+s+span_RHS } return s }, // MD5('default') //
}
var padSP = {
    'lsup':1,
    'lsub':1,
    'csup':1,
    'csub':1,
    'dot':1,
    'ddot':1,
    'dddot':1,
    'vec':1,
    'lim':1,
    'sum':1,
    'prod':1,
    'coprod':1,
    'int':1,
    'iint':1,
    'iiint':1,
    'lint':1,
    'llint':1,
    'lllint':1,
    'evaluate':1,
    'evaluated':1,
}
var lineCOUNT = 0
function getNUM(n){
    var n = arguments[0]
    if(n<10){
        n = '000'+n
    } else if(n<100){
        n = '00'+n
    } else if(n<1000){
        n = '0'+n
    }
    return n
}
function render(obj){
    var src=obj.src
    var targ=obj.targ
    var err=obj.err
    var status = {
        true:function(v){
            srcTranslated.innerText = v
        },
        false:function(v){
            var s = v.map(function(r,i){
                var tdCOUNT = 0
                var tdUPPER = ''
                var tdLOWER = ''
                var tdUPPERSTACK = []
                var tdLOWERSTACK = []
                r.pc = 0
                r = r.map(function(d,j,me){
                    if(j>=me.pc){
                        var val = d.val
                        if(buildSYMBOL[val]){
                            val = buildSYMBOL[val](me,j)
                        } else if(val){
                            val = buildSYMBOL['C21F969B5F03D33D43E04F8F136E7682'](me,j) // MD5('default') //
                        }
                    }
                    if(me.pc==j){
                        me.pc++
                    }
                    if(padSP[d.val]){
                        val = '</td><td>'+val+'</td><td>'
                    }
                    if(d.tdUPPER || d.tdLOWER){
                        if(d.tdUPPER){
                            tdUPPERSTACK.push('')
                            tdUPPERSTACK.push(d.tdUPPER)
                        } else {
                            tdUPPERSTACK.push('')
                            tdUPPERSTACK.push('')
                        }
                        if(d.tdLOWER){
                            tdLOWERSTACK.push('')
                            tdLOWERSTACK.push(d.tdLOWER)
                        } else {
                            tdLOWERSTACK.push('')
                            tdLOWERSTACK.push('')
                        }
                    }
                    if(val && val.match(/<td/)){ // lineup for r //
                        tdCOUNT += val.match(/<td/g).length
                        while(tdUPPERSTACK.length<tdCOUNT || tdLOWERSTACK.length<tdCOUNT){
                            if(tdUPPERSTACK.length<tdCOUNT){
                                tdUPPERSTACK.push('')
                            }
                            if(tdLOWERSTACK.length<tdCOUNT){
                                tdLOWERSTACK.push('')
                            }
                        }
                    }
                    return val
                }).join(' ')
                tdUPPERSTACK.push('</td><td>') // lineup for lineCOUNT //
                tdLOWERSTACK.push('</td><td>') // lineup for lineCOUNT //
                tdUPPER = tdUPPERSTACK.join('</td><td>')
                tdLOWER = tdLOWERSTACK.join('</td><td>')
                var result = (`<table class=cssTABLE><tbody class="cssFormulaFont"><tr class="cssUBOUNDS"><td>${tdUPPER}</td></tr><tr class="cssFormula"><td>${r}</td><td class="cssLINE">(${getNUM(lineCOUNT)})</td></tr><tr class="cssLBOUNDS"><td>${tdLOWER}</td></tr></tbody></table>`)
                lineCOUNT++ // = Math.max(lineCOUNT,(i+1))
                return result
            }).join('\n')
            targ.innerHTML = s
        },
    }
    status[(err==true)](src)
}
function __reportstatus_ThreadWorker_00(e){
    if(!e.data.error){
        if(e.data.origin == 'ThreadWorker_00'){
            srcTranslated.innerText += e.data.value.join('\n') //e.data.value[0] + '\n'
            //render( e.data )
        } else {
            srcTranslated.innerText += e.data.value
        }
    } else {
        srcTranslated.innerText = e.data.value
    }
}
function euclid_reset()
{
    lineCOUNT = 0
}
function _reset(){
    loader('force')
    preview_render({ srcElement:{id:"axmEditor"} })
}
function loader(forceReset) {
    euclid_reset()
    if(forceReset || !axmEditor.innerText){
        axmEditor.innerText = 'int from 0 to 5 { x raised c dx } = c cdot x raised { ( c minus 1 ) }, given c greaterthan 0'
    }
    srcTranslated.innerText = ''
    var s = ''
    var TAG00 = '<option>  '
    var TAG01 = '  </option>\n'
    symbolsMAP.forEach(function(v){ s += TAG00 + v.replace(/^__.*/,'__________________') + ' ' + symbolsMAP[v] + TAG01; return v; })
    txtHELP.innerHTML = s
    selBox.innerHTML = s
    spnWindowTitle.innerHTML = ' \u221d Euclid Automated Prover'
}
function clear_window() { // clear_window () //
    euclid_reset()
    srcTranslated.innerText = ''
}
function MD5() { // generate_MD5 () //
    var obj = [srcTranslated.innerText]
    obj.push('Message Digest v5 Verification key\n'+Math.md5(srcTranslated.innerText) )
    srcTranslated.innerText = obj.join('\n\n')
}
function entag(N) {
    var p = N.replace(/\n$/,'').split(/\n/)
    buffer = p.map(function(v){
        return v.replace(/(^\w+|\W+|==|\|\|&&)/g, ' $1 ').replace(/([_'"\{\}\[\]\(\)])/gm,' $1 ').replace(/##+/g,' ## ')
    });
    var s = buffer.map(function(v){
        return v.split(/\s+/)
    });
    return s.map(function(v){
        var q=[];
        v.map(function(k){
            if(k){
                obj = {}
                obj.tok = 0
                obj.val = k
                obj.id = 0
                q.push(obj)
            }
        })
        return q
    });
}
function preview() {
    euclid_reset()
    var u = [];
    var v = [];
    var z = [];
    axmEditor.innerText.split(/\n+/g).map((w,i,me)=>{
        if(w.match(/<==|<==>|==>/)){
            u.push(w)
            w=''
        } else if (w) {
            v.push(w)
        }
        return w
    });
    u.length && render({ src:entag(u.join('\n')),targ:lemmaEditor })
    v.length && render({ src:entag(v.join('\n')),targ:formulaTBL })
}
function preview_render(e){
    if(e.srcElement.id=="axmEditor"){
        preview()
    }
}
addEventListener("keyup",preview_render,false)
function translatorTool() {
    try{
        euclid_reset()
    } catch (e) {
        srcTranslated.innerText = e
    }
}