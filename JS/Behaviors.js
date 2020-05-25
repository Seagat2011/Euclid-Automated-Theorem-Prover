/*

  TITLE: 
  Behaviors.js 

  AUTHOR: Seagat2011 
  http://eterna.cmu.edu/web/player/90270/
  http://fold.it/port/user/1992490

  DESCRIPTION: 
  Main (math) operations interface to euclid and its components
  to operate on numbers of infinite magnitude

  UPDATED
  +Number to string conversion
  +Available operations (add,multiply)
  +Revised internal number representation (performance)
  +Add algorithm uses lookup table reference (performance)
  -euclid_operation

  REFERENCES:

  INPUT:
24642324324586858756587657658756785857656856756554563432456458796987907097897987656745632232322453654587657860979088768689687665654563543543453647658757865586987698698686897968966986796768656565465343
16246896856757858685875658765765875678585765685675655456343245645877656757658757856669070978979876567456322323224536545876578609790887686896876656545635435434536476587578655869876986986868979689669867
29485749579823759024785923475923475982347598374589273495723498572983475892734598723498579823475892745982374895723498578293475892347598243759827345987243895723489574875894375987234985729483758247598723

  OUTPUT:
11804953080793687218220190712516551324312634864687505210880808771314809449692208436876194384822271357708184535031717068027959841685429128770664233790575880181679985350037523448486097718617832567778737534676386124052291686410471997463434121421588141460555244509176786829246055978175931659333253534905800361156299682852152103254722679689866619497054325800247067107849860786054919813401919938339579178438022507677991107934204473718886622143004966625541530093868693170788752561078386496097003370376576911112647265188701955514490810002933469492281469228900929776468933786077161401405420159052875538550463
  
  SCRIPT TYPE: 
  Euclid Tool

*/
Object.prototype.padBlock = function(i,u){
    var self = (this.toString()).split('')
	var I = self.length
    while(i-->I)
        self.unshift(u)
    return self.join('')
}
Object.prototype.totalTicks = function(){
	var dte = this.map((u)=>{
		u[0]=Number(u[0])
		u[1]=Number(u[1])
		u[2]=Number(u[2])
		return u
	});
	var I = dte.length - 1
	while(1){
		var next = ''
		if(dte[I][1]<dte[0][1]){
			dte[I][0]--
			dte[I][1]+=60
			next += '1'
		}
		if(dte[I][2]<dte[0][2]){
			dte[I][1]--
			dte[I][2]+=60
			next += '1'
		}
		if(!next)
			break
	}
	return `${(dte[I][0]-dte[0][0]).padBlock(2,'0')}h ${(dte[I][1]-dte[0][1]).padBlock(2,'0')}m ${(dte[I][2]-dte[0][2]).padBlock(2,'0')}s`
}
Object.prototype.getTick = function(){
	return (Date().toString()).match(/(\d+:\d+:\d+)/)[0].split(/:/)
}
Object.prototype.padLZero = function(i){
    var self = this
    while(i--)
        self.unshift('0')
    return self
}
Object.prototype.Zero = function(){
    var self = this
    return self.map((u,i,me)=>{
        return '0'
    })
}
Object.prototype.unpadLZero = function(){
    var self = this
    var i = this.length - 1
    while((self[i--] == '0') && !self[i].match(/\./))
        self.pop()
    return self
}
Object.prototype.asReverseArray = function(){
	return this.split('').reverse()
}
Object.prototype.splitLines = function(){
    var ret = []
    var self = this
    self
    .split(/\n+/g)
    .map((u,i,me)=>{
        if(u){
            ret.push(u)
        }
        return u
    });
	return ret
}
Object.prototype.getIDX = function(i){
	return this[i] || '0'
}
Object.prototype.asLONG = function(){
	return this.unpadLZero().reverse().join('')
}
Object.prototype.getDecimal = function(u){
	return this.replace(/\./,(_,i,me)=>{ 
		u.dot += (me.length-i-1)
		return ''
	})
}
Object.prototype.placeDecimal = function(u){
	var self = this
	if(u.dot){
		var w = self[u.dot]
		self[u.dot] = `${w}.`
	}
	return self
}
var AWC = { /* Add With Carry : ( op1.op2.carry.result : carry.result ) */  }
var DWC = { /* Divide With Carry : ( op1.op2.carry.result : carry.result ) */ }
var MWC = { /* Multiply With Carry : ( op1.op2.carry.result : carry.result ) */ }
var SWC = { /* Subtract With Carry : ( op1.op2.carry.result : carry.result ) */ }
for(var i=0;i<1e4;i++){
    var u=i.toString().padBlock(4,'0')
    var w=u.split('').map((v)=>{
        return Number(v)
    });
    AWC[u]=((w[0]+w[1])+(w[2]+w[3])).toString().padBlock(2,'0')
    DWC[u]=parseInt((w[0]/w[1])+(w[2]+w[3])).toString().padBlock(2,'0')
    MWC[u]=((w[0]*w[1])+(w[2]+w[3])).toString().padBlock(2,'0')
    SWC[u]=Math.abs((w[0]-w[1])+(w[2]+w[3])).toString().padBlock(2,'0')
}
function MULTIPLY(src,targ,divTimer){
	if(src.gLAST==src.innerText.replace(/\n+/g,'\n'))
		return
	var RET = '';
	var dte = [RET.getTick()]
	var decimalPoint = { dot:0 }
	try {
		var RESULT = [];
		var operands = src.innerText.splitLines();
		operands.map((op1,m,meOne)=>{
			if(m != 0){
				var carry = '0'
				var LHS = []
				var RHS = op1.getDecimal(decimalPoint).asReverseArray()
				LHS.padLZero(op1.length)
				RHS.map((u,i,meTwo)=>{
					var idx
					RESULT.map((v,j,meThree)=>{
						idx = (i+j)
						var w = u + v + carry + LHS.getIDX(idx)
						var y = MWC[w]
						carry = y[0]
						LHS[idx] = y[1]
						return v
					});
					if(carry > '0'){
						idx++
						var w = '00' + carry + LHS.getIDX(idx)
						var y = MWC[w]
						LHS[idx] = y[1]
						carry = '0'
					}
					return u
				});
				RESULT = LHS
			} else {
				RESULT = [...op1.getDecimal(decimalPoint).asReverseArray()]
			}
			return op1
		});
		RET = RESULT.placeDecimal(decimalPoint).asLONG()
		src.gLAST=src.innerText.replace(/\n+/g,'\n') // SUCCESS //
	} catch(e) {
		RET = e
	}
    targ.innerText = RET
	dte.push(RET.getTick())
	divTimer.innerText = dte.totalTicks()
}