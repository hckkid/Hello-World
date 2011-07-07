signature SET = sig
	type ''a myset = ''a list
	val belongs : ''a*(''a list) -> bool
	val makeSet : ''a list -> ''a myset
	val additem : ''a*(''a list) -> ''a myset
	val addlist : (''a list)*(''a myset) -> ''a myset
	val union : (''a myset)*(''a myset) -> ''a myset
	val intersection : (''a myset)*(''a myset) -> ''a myset
	val getlist : ''a myset -> ''a list
	val addToAll : ''a*''a myset myset -> ''a myset myset
	val powerSet : ''a myset -> ''a myset myset
end
structure Set :> SET = struct
	type ''a myset = ''a list
	fun belongs (x,[]) = false
		| belongs (x,y::ys) = if (x=y) then true else belongs(x,ys)
	fun makeSet [] = []
		| makeSet (x::xs) =
			let
				val tmpst = makeSet xs
				fun adder(z) = 
					if (belongs(z,tmpst)) then tmpst
					else z::tmpst
			in adder(x)
			end
	fun additem (x,tmpst) = if (belongs(x,tmpst)) then tmpst else x::tmpst
	fun addlist ([],tmpst) = tmpst
		| addlist (x::xs,tmpst) = additem(x,addlist(xs,tmpst))
	fun union ([],tmpst) = tmpst
		| union (x::xs,tmpst) = additem(x,union(xs,tmpst))
	fun intersection ([],tmpst) = nil
		| intersection (x::xs,tmpst) = if (belongs(x,tmpst)) then x::intersection(xs,tmpst) else intersection(xs,tmpst)
	fun getlist [] = []
		| getlist (x::xs) = x::xs
	fun addToAll (x,[]) = []
		| addToAll (x,y::ys) = additem(x,y)::addToAll(x,ys)
	fun powerSet [] = [[]]
		| powerSet (x::xs) = (powerSet(xs)@addToAll(x,powerSet(xs)))
end
signature FORM = sig
	datatype form =
		Absurdum | propSymb of char | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form
	exception SyntaxError of string
	val getpropSymbs : form -> char Set.myset
	val parse : string -> form
	val format : form -> string
end
structure Form :> FORM = struct
	datatype token =
		LogicalAbsurdum | Literal of char | LogicalNot |
		LogicalAnd | LogicalOr | LogicalImplies | LParen | RParen
	exception LexicalError
	fun tokenize [] = []
		| tokenize ( #"-" :: #">" :: cs) = (LogicalImplies :: tokenize(cs))
		| tokenize ( #"-" :: c :: cs) = raise LexicalError
		| tokenize ( #"&" :: #"&" :: cs) = (LogicalAnd :: tokenize(cs))
		| tokenize ( #"&" :: c :: cs) = raise LexicalError
		| tokenize ( #"|" :: #"|" :: cs) = (LogicalOr :: tokenize(cs))
		| tokenize ( #"|" :: c :: cs) = raise LexicalError
		| tokenize ( #"!" :: cs) = (LogicalNot :: tokenize(cs))
		| tokenize ( #"_" :: cs) = (LogicalAbsurdum :: tokenize(cs))
		| tokenize ( #"(" :: cs) = (LParen :: tokenize(cs))
		| tokenize ( #")" :: cs) = (RParen :: tokenize(cs))
		| tokenize (c :: cs) = Literal c :: tokenize(cs)
	datatype form =
		Absurdum | propSymb of char | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form
	exception SyntaxError of string
	fun getpropSymbs Absurdum = []
		| getpropSymbs (propSymb c) = [c]
		| getpropSymbs (Negation A) = getpropSymbs(A)
		| getpropSymbs (Conjunction(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
		| getpropSymbs (Disjunction(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
		| getpropSymbs (Implication(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
	fun parse_imp fm = 
		let
			val ( f , fm') = parse_or fm
		in
			case fm'
				of (LogicalImplies :: fm'') =>
					let
						val ( f' , fm''') = parse_imp fm''
					in
						(Implication ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_or fm = 
		let
			val ( f , fm') = parse_and fm
		in
			case fm'
				of (LogicalOr :: fm'') =>
					let
						val ( f' , fm''') = parse_or fm''
					in
						(Disjunction ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_and fm = 
		let
			val ( f , fm') = parse_atom fm
		in
			case fm'
				of (LogicalAnd :: fm'') =>
					let
						val ( f' , fm''') = parse_and fm''
					in
						(Conjunction ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_atom nil = raise SyntaxError ("Factor Expected \n")
		| parse_atom (LogicalNot :: fm) = 
			let
				val ( f , fm') = parse_atom fm
			in
				(Negation f , fm')
			end
		| parse_atom ((Literal f) :: fm) = (propSymb f , fm)
		| parse_atom (LogicalAbsurdum :: fm) = (Absurdum , fm)
		| parse_atom (Lparen :: fm) =
			let
				val ( f , fm') = parse_imp fm
			in
				case fm'
					of nil => raise SyntaxError ("Right Parenthesis Expected .\n")
					| (RParen :: fm'') => ( f , fm'')
					| _ => raise SyntaxError ("Right Parenthesis Expected .\n")
			end
	fun parse s =
		let
			val ( f , fm) = parse_imp (tokenize (String.explode s))
		in
			case fm
				of nil => f
				| _ => raise SyntaxError ("Unexpected Input .\n")
		end
		handle LexicalError => raise SyntaxError ("Invalid Input .\n")
	fun format_exp Absurdum = [#"_"]
		| format_exp (propSymb P) = [P]
		| format_exp (Negation A) = 
			let
				val s = format_exp A
			in ([#"("] @ [#"!"] @ s @ [#")"])
			end
		| format_exp (Conjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in [#"("] @ n @ [#"&"] @ [#"&"] @ n' @ [#")"]
			end
		| format_exp (Disjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"|"] @ [#"|"] @ n' @ [#")"])
			end
		| format_exp (Implication (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"-"] @ [#">"] @ n' @ [#")"])
			end
	fun format f = String.implode (format_exp f)
end
signature sem1 = sig
	exception IncompleteValuation
	exception wrongFormula
	val valuation : (char*char) list -> (Form.form*bool) Set.myset
	val interperation : (Form.form*bool) Set.myset*Form.form -> bool
end
structure Sem1 :> sem1 = struct
	exception wrongFormula
	exception IncompleteValuation
	fun valuation [] = []
		| valuation((p:char,q:char)::xs) = (Form.propSymb p,(if (q = #"T") then true else false))::valuation(xs)
	fun interperation (valu,Form.Absurdum) = false
		| interperation (valu,Form.propSymb c) = (if (Set.belongs((Form.propSymb c,true),valu)) then true else false)
		| interperation (valu,Form.Negation p) = not(interperation(valu,p))
		| interperation (valu,Form.Conjunction(A,B)) = (interperation(valu,A) andalso interperation(valu,B))
		| interperation (valu,Form.Disjunction(A,B)) = ((interperation(valu,A)) orelse (interperation(valu,B)))
		| interperation (valu,Form.Implication(A,B)) = (((not(interperation(valu,A)))) orelse (interperation(valu,B)))
end
signature semantic = sig
	val getModel : char list -> Form.form Set.myset
	val validates : Form.form Set.myset*Form.form -> bool
end
structure Semantic :> semantic = struct
	fun getModel [] = []
		| getModel (x::xs) = (Form.propSymb(x))::(getModel xs)
	fun validates (M,Form.Absurdum) = false
		| validates (M,Form.propSymb c) = (if (Set.belongs(Form.propSymb c,M)) then true else false)
		| validates (M,Form.Negation p) = not(validates(M,p))
		| validates (M,Form.Conjunction(A,B)) = (validates(M,A) andalso validates(M,B))
		| validates (M,Form.Disjunction(A,B)) = ((validates(M,A)) orelse (validates(M,B)))
		| validates (M,Form.Implication(A,B)) = (((not(validates(M,A)))) orelse (validates(M,B)))
end
signature normalForms = sig
	val toNNF : Form.form -> Form.form
	val toCNF : Form.form -> Form.form
	val toDNF : Form.form -> Form.form
end
structure NormalForms :> normalForms = struct
	fun toNNF Form.Absurdum = Form.Absurdum
		| toNNF (Form.propSymb c) = (Form.propSymb c)
		| toNNF (Form.Negation(Form.propSymb c)) = Form.Negation(Form.propSymb(c))
		| toNNF (Form.Negation(Form.Absurdum)) = Form.Negation(Form.Absurdum)
		| toNNF (Form.Negation(Form.Negation(A))) = toNNF(A)
		| toNNF (Form.Negation(Form.Conjunction(A,B))) = Form.Disjunction(toNNF(Form.Negation(A)),toNNF(Form.Negation(B)))
		| toNNF (Form.Negation(Form.Disjunction(A,B))) = Form.Conjunction(toNNF(Form.Negation(A)),toNNF(Form.Negation(B)))
		| toNNF (Form.Negation(A)) = toNNF(Form.Negation(toNNF(A)))
		| toNNF (Form.Conjunction(A,B)) = Form.Conjunction(toNNF(A),toNNF(B))
		| toNNF (Form.Disjunction(A,B)) = Form.Disjunction(toNNF(A),toNNF(B))
		| toNNF (Form.Implication(A,B)) = Form.Disjunction(toNNF(Form.Negation(A)),toNNF(B))
	fun toCNF fm=
		let
			val fm' = toNNF(fm)
			fun toCNFn Form.Absurdum = Form.Absurdum
				| toCNFn (Form.propSymb c) = (Form.propSymb c)
				| toCNFn (Form.Negation(A)) = Form.Negation(A)
				| toCNFn (Form.Conjunction(A,B)) = Form.Conjunction(toCNFn(A),toCNFn(B))
				| toCNFn (Form.Disjunction(A,B)) = 
					let
						val A' = toCNFn(A)
						val B' = toCNFn(B)
						fun tmpDis (a,Form.Conjunction(b,c)) = Form.Conjunction(toCNFn(Form.Disjunction(a,b)),toCNFn(Form.Disjunction(a,c)))
							| tmpDis (Form.Conjunction(a,b),c) = Form.Conjunction(toCNFn(Form.Disjunction(a,c)),toCNFn(Form.Disjunction(b,c)))
							| tmpDis (a,b) = Form.Disjunction(a,b)
					in tmpDis(A',B')
					end
			in toCNFn(fm')
		end
	fun toDNF fm=
		let
			val fm' = toNNF(fm)
			fun toDNFn Form.Absurdum = Form.Absurdum
				| toDNFn (Form.propSymb c) = (Form.propSymb c)
				| toDNFn (Form.Negation(A)) = Form.Negation(A)
				| toDNFn (Form.Disjunction(A,B)) = Form.Disjunction(toDNFn(A),toDNFn(B))
				| toDNFn (Form.Conjunction(A,B)) = 
					let
						val A' = toDNFn(A)
						val B' = toDNFn(B)
						fun tmpCon (a,Form.Disjunction(b,c)) = Form.Disjunction(toDNFn(Form.Conjunction(a,b)),toDNFn(Form.Conjunction(a,c)))
							| tmpCon (Form.Disjunction(a,b),c) = Form.Disjunction(toDNFn(Form.Conjunction(a,c)),toDNFn(Form.Conjunction(b,c)))
							| tmpCon (a,b) = Form.Conjunction(a,b)
					in tmpCon(A',B')
					end
			in toDNFn(fm')
		end
end
signature proofSystem = sig
	val isTautology : Form.form -> bool
	val isContradiction : Form.form -> bool
	val areEquivalent : Form.form*Form.form -> bool
	val isValidCNF : Form.form -> bool
end
structure ProofSystem :> proofSystem = struct
	fun isTautology f =
		let
			val x = Form.getpropSymbs(f)
			val px = Set.powerSet(x)
			val pm = 
				let
					fun Powm [] = []
						| Powm (y::ys) = (Semantic.getModel(y)::Powm(ys))
				in Powm(px)
				end
			fun tauto (f',[]) = true
				| tauto (f',z::zs) = if (Semantic.validates(z,f') = true) then tauto(f',zs) else false
		in tauto(f,pm)
		end
	fun isContradiction f =
		let
			val x = Form.getpropSymbs(f)
			val px = Set.powerSet(x)
			val pm = 
				let
					fun Powm [] = []
						| Powm (y::ys) = (Semantic.getModel(y)::Powm(ys))
				in Powm(px)
				end
			fun tauto (f',[]) = true
				| tauto (f',z::zs) = if (Semantic.validates(z,f') = false) then tauto(f',zs) else false
		in tauto(f,pm)
		end
	fun areEquivalent (f1,f2) = if (isTautology(Form.Implication(f1,f2)) andalso isTautology(Form.Implication(f1,f2))) then true else false
	fun isValidCNF(f)=
		let
			val f' = NormalForms.toCNF(f)
			fun tmpValid (Form.Conjunction(A,B)) = (tmpValid(A) andalso tmpValid(B))
			| tmpValid (Form.Absurdum) = false
			| tmpValid (Form.propSymb c) = false
			| tmpValid (Form.Negation(Form.Absurdum)) = true
			| tmpValid (Form.Negation(Form.propSymb c)) = false
			| tmpValid (f) = 
				let 
					fun lister (Form.Absurdum) = ([],[],false)
						| lister (Form.propSymb c) = (Set.makeSet([c]),[],false)
						| lister (Form.Negation(Form.Absurdum)) = ([],[],true)
						| lister (Form.Negation(Form.propSymb c)) = ([],Set.makeSet([c]),false)
						| lister (Form.Disjunction(A',B')) =
							let
								val (plst1,nplst1,flag1) = lister(A')
								val (plst2,nplst2,flag2) = lister(B')
							in ( Set.union(plst1,plst2) , Set.union(nplst1,nplst2) , (flag1 orelse flag2))
							end
					fun validater (x) =
						let
							val (plst,nplst,flag) = lister(x)
							val cmmn = Set.intersection(plst,nplst)
						in (flag orelse (not (cmmn = [])))
						end
				in validater(f)
				end
		in tmpValid(f')
		end
end