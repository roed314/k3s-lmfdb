
declare type GenSym[pSym];

declare attributes pSym:
	p,
	Scale,
	Sign,
	Dimension,
	HasOddOnDiagonal,
	Oddity;

declare attributes GenSym:
	pSymbols,
	Disc,
	Rank,
	Sign;

intrinsic pSymbol(p::RngIntElt, i::RngIntElt, eps::RngIntElt, n::RngIntElt) -> pSym
{.}
    ret := New(pSym);
    ret`p := p;
    ret`Scale := i;
    ret`Sign := eps;
    ret`Dimension := n;
    return ret;
end intrinsic;

intrinsic twoSymbol(i::RngIntElt, eps::RngIntElt, n::RngIntElt, odd_diag::BoolElt, oddity::RngIntElt) -> pSym
{.}
    ret := New(pSym);
    ret`p := 2;
    ret`Scale := i;
    ret`Sign := eps;
    ret`Dimension := n;
    ret`HasOddOnDiagonal := odd_diag;
    ret`Oddity := oddity;
    return ret;
end intrinsic;

intrinsic twoSymbol(i::RngIntElt, eps::RngIntElt, n::RngIntElt) -> pSym
{.}
    ret := New(pSym);
    ret`p := 2;
    ret`Scale := i;
    ret`Sign := eps;
    ret`Dimension := n;
    ret`HasOddOnDiagonal := false;
    ret`Oddity := 0;
    return ret;
end intrinsic;

intrinsic Dimension(pSymbol::pSym) -> RngIntElt
{.}
    return pSym`Dimension;
end intrinsic;

intrinsic Scale(pSymbol::pSym) -> RngIntElt
{.}
    return pSym`Scale;
end intrinsic;

intrinsic Sign(pSymbol::pSym) -> RngIntElt
{.}
    return pSym`Sign;
end intrinsic;

intrinsic Oddity(pSymbol::pSym) -> RngIntElt
{.}
    require pSymbol`p eq 2 : "Oddity only defined when p = 2";
    return pSym`Oddity;
end intrinsic;

intrinsic SymbolType(pSymbol::pSym) -> RngIntElt
{.}
    require pSymbol`p eq 2 : "Type only defined when p = 2";
    return pSym`HasOddOnDiagonal select 1 else 2;
end intrinsic;

// disc can be read off from the symbols
intrinsic GenusSymbol(disc::RngIntElt, n_plus::RngIntElt, n_minus::RngIntElt, pSymbols::SeqEnum[pSym]) -> GenSym
{.}
    ret := New(GenSym);
    ret`Disc := disc;
    ret`pSymbols := AssociativeArray();
    for psym in pSymbols do
	if not IsDefined(ret`pSymbols, psym`p) then
	    ret`pSymbols[psym`p] := [];
	end if;
	Append(~ret`pSymbols[psym`p], psym);
    end for;
    ret`Sign := n_plus - n_minus;
    ret`Rank := n_plus + n_minus;
    return ret;
end intrinsic;

intrinsic pSymbols(gs::GenSym) -> SeqEnum[pSym]
{.}
    return gs`pSymbols;
end intrinsic;

intrinsic Discriminant(gs::GenSym) -> SeqEnum[pSym]
{.}
    return gs`Disc;
end intrinsic;

intrinsic Signature(gs::GenSym) -> SeqEnum[pSym]
{.}
    return gs`Sign;
end intrinsic;

intrinsic Rank(gs::GenSym) -> SeqEnum[pSym]
{.}
    return gs`Rank;
end intrinsic;

intrinsic DeterminantCondition(gs::GenSym, p::RngIntElt) -> BoolElt
{.}
    _, cpr := Valuation(Discriminant(gs),p);
    return LegendreSymbol(cpr, p) eq &*[Sign(psym) : psym in Symbols(gs)[p]];
end intrinsic;

intrinsic DeterminantCondition(gs::GenSym) -> BoolElt
{.}
    return &and[DeterminantCondition(gs,p) : p in Keys(Symbols(gs))];
end intrinsic;

intrinsic OddityCondition(gs::GenSym) -> BoolElt
{.}
    
end intrinsic;
