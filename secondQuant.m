(* ::Package:: *)

(* Mathematica Package *)
(* secondQuant v 0.1 
   Created by Alexandre Miguel de Ara\[UAcute]jo Lopes <aalopes@ovi.com>
   Universit\[ADoubleDot]t Freiburg, 30/06/13 
   Some functions have been adapted from W. Kinzel, G. Reents, Physics by computer, Springer, 1996

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)


(* Some notes:

If one only wants to make use of the operators c, cdagger and n and the vacuum state and the scalar product, we can actually work in Fock space.
To make use of basisGen, one needs to confine itself to a layer of the Fock space with a given number of spin up particles and spin down particles.
Every function that makes use of basisGen works only inside a Fock layer.

*)


(* Missing:

* Defining boundary conditions
* How to calculate matrix elements using basis (maybe just input the operator in terms 
of c and c dagger and spit the matrix elements).
* Invalid function arguments and throwing errors - sanity checks for checking in which form the state is given, etc... - this is of utmost importance to avoid erros
*)

(* Normal ordering:
cdagger[1,up]...cdagger[N,up]...c[1,down]...cdagger[N-1,down]cdagger[N,down] |vacuum>
*)


BeginPackage["secondQuant`"]


cdagger::usage        = "cdagger[mode, spin][state] creation operator"
c::usage              = "c[mode, spin][state] annihilation operator "
n::usage              = "n[state] number operator "
vac::usage            = "vac[nModes] vacuum state for nModes modes where cdagger,c or n can act"
scalarProduct::usage  = "scalarProduct[state1,state2] scalar product between state1 and state2 - both viewed as kets."
scalarProduct1::usage = "scalarProduct1[state1,state2,basis] non-recursive implementation of the scalar product which can be much faster
                         however one should calculate all these things related to the basis before invoking the function, otherwise it will take
                         too long when using this function several times"
basisGen::usage       = "basisGen[nSites,nSpinUp,nSpinDown] generates a basis for the space of "
lenBasis::usage       = "lenBasis[basis] returns the size of the basis used"
matrixForm::usage     = "matrixForm[op,bas] generates the matrix form of operator op in basis bas"
rdm::usage            = "rdm[state,spin,modes] creates the 1PRDM, rho_{ij} = <psi|cdagger_i c_j|psi>, for the pure 
                         state state, for a given spin - only valid if rho psi has a well defined number of spin-up 
                         and spin-down particles in which case rho is a direct sum of rho_up and rho_down. modes is simply the number of modes of the system"
bToz::usage           = "bToz[state] converts from the b-form (bracket) of a state, {{...},{...}} to the z-form of a state, z[{{...},{...}}]
                          where the first bracket gives us the occupation numbers for spins-up and the right for spins-down."
zTob::usage           = "zTob[state] converts from the z-form of a state, z[{{...},{...}}] to the b-form (bracket) of a state, {{...},{...}} 
                          where the first bracket gives us the occupation numbers for spins-up and the right for spins-down."
eToz::usage           = "eToz[state,basis] convert an arbitrary state written in e-form, i.e. {c_1,...,c_N}, where c_i are the expansion coefficients 
                       of state state in basis basis to a its z-form, i.e. sum_i{c_i z[i]}, where z[i] denotes the ith basis state in written in z-form."
zToe::usage           = "zToe[state,basis] convert an arbitrary state written in z-form, i.e. sum_i{c_i z[i]}, where z[i] denotes the ith basis state in 
                         written in z-form to e-Form i.e. {c_1,...,c_N}, where c_i are the expansion coefficients of state state in basis basis."



(* Begin["`Private`"] *)


(* ::Subsection:: *)
(*defining cdagger and c, n*)


(* ::Subsubsection:: *)
(*auxiliary definitions*)


add[k_, sigma_][arg_] := ReplacePart[arg, 1, {sigma, k}]


remove[k_, sigma_][arg_] := ReplacePart[arg, 0, {sigma, k}]


sgn[k_, sigma_, arg_] := Module[
{nSpinUp},
nSpinUp = Total[arg[[1]]];
(-1)^(nSpinUp*(sigma - 1))*(-1)^(Sum[arg[[sigma, j]], {j, k - 1}])
]


(* ::Subsubsection:: *)
(*Defining cdagger and c*)


(* ::Text:: *)
(*Definition of creation, annihilation operators and number operator. Here factor_. z[arg] searches for a "pattern" and leaves it untouched. Otherwise it would sum list elements element-wise, which is not what we want, since summing states does not consist in that. The . before z means that if there is no factor in the RHS expression, we assume factor_ = 1.*)


(* ::Text:: *)
(*Note - periodic boundary conditions need to be introduced manually!*)


(* ::Subsubsection:: *)
(*Defining linearity*)


cdagger[k_,sigma_][arg1_+arg2_]:=cdagger[k,sigma][arg1] +cdagger[k,sigma][arg2] 


c[k_,sigma_][arg1_+arg2_]:=c[k,sigma][arg1] +c[k,sigma][arg2] 


n[k_,sigma_][arg1_+ arg2_]:=n[k,sigma][arg1] + n[k,sigma][arg2]


(* ::Subsubsection:: *)
(*Defining operation on the null vector*)


(* ::Text:: *)
(*Integer zero case*)


cdagger[k_,sigma_][0]:=0


c[k_,sigma_][0]:=0


n[k_,sigma_][0]:=0


(* ::Text:: *)
(*Real zero case*)


cdagger[k_,sigma_][0.]:=0


c[k_,sigma_][0.]:=0


n[k_,sigma_][0.]:=0


(* ::Text:: *)
(*Complex zero case*)


cdagger[k_,sigma_][0.+0. I] :=0


c[k_,sigma_][0.+0. I] :=0


n[k_,sigma_][0.+0.I]:=0


cdagger[k_, sigma_][factor_. z[arg_]] := factor*(1 - arg[[sigma, k]])*sgn[k, sigma, arg]*z[add[k, sigma][arg]]


c[k_,sigma_][factor_. z[arg_]]:=factor*arg[[sigma,k]]*sgn[k,sigma,arg]*z[remove[k,sigma][arg]]


n[k_,sigma_][factor_. z[arg_]]:=factor*arg[[sigma,k]]*z[arg]


(* ::Subsection:: *)
(*Defining scalar product*)


(* ::Text:: *)
(*scalarProduct( factor1 |arg1>, factor2 |arg2> ) = Conjugate[factor1] factor2 <arg1|arg2>*)


scalarProduct[factor1_. z[arg1_],factor2_. z[arg2_]]:=Conjugate[factor1]*factor2*If[arg1==arg2,1,0]


(* ::Subsubsection:: *)
(*Null vector*)


(* ::Text:: *)
(*Integer zero*)


scalarProduct[a_, 0] := 0


scalarProduct[0, a_] := 0


(* ::Text:: *)
(*Real zero*)


scalarProduct[a_, 0.] := 0


scalarProduct[0., a_] := 0


(* ::Text:: *)
(*Complex zero*)


scalarProduct[a_, 0.+0. I] := 0


scalarProduct[0.+0. I, a_] := 0


(* ::Subsubsection:: *)
(*distrubutive in both arguments*)


scalarProduct[a_, b_ + c_] := scalarProduct[a, b] + scalarProduct[a, c]


scalarProduct[a_ + b_, c_] := scalarProduct[a, c] + scalarProduct[b, c]


(* ::Subsection:: *)
(*Defining another scalar product*)


(* ::Text:: *)
(*This one makes use of Mathematica's own inner product and is actually faster in some situations since the function scalarProduct we have defined is recursive (due to distributivity) and can be extremely slow*)


scalarProduct1[vec1_,vec2_,basis_] := Module[
{lenBasis, zBasis, basisAux, basisNew, rule, bra, ket
},
lenBasis = Length[basis];
zBasis =  Table[z[basis[[i]]],{i,1,lenBasis}];
basisAux = ConstantArray[0,lenBasis];
basisAux[[1]] = 1;
basisNew = Permutations[basisAux];
rule = Table[zBasis[[i]]->basisNew[[i]],{i,1,lenBasis}];
bra = Conjugate[vec1/.rule];
ket = vec2/.rule;
bra.ket
]


(* ::Subsection:: *)
(*Defining vacuum state (requires number of sites/modes)*)


vac[sites_] := {ConstantArray[0,sites],ConstantArray[0,sites]};


(* ::Subsection:: *)
(*Defining basis - for a system with a fixed number of spins and sites/modes (requires total number of particles, up spins and down spins )*)


basisGen[sites_,spinup_,spindown_] := Module[
{up = Permutations[Table[If[j <= spinup, 1, 0], {j, sites}]],
down = Permutations[Table[If[j <= spindown, 1, 0], {j, sites}]]},
 Flatten[Table[{up[[i]], down[[j]]}, {i, Length[up]}, {j, Length[down]}], 1]
]


(* ::Subsection:: *)
(*Calculating the matrix form of an operator defined in terms of c and cdagger, using a basis given by the function basis.*)


matrixForm[op_,basis_]:=Module[
{lenBasis,
opKet
},
lenBasis = Length[basis];
opKet = Table[op[z[basis[[i]]]],{i,Length[basis]}];
Table[scalarProduct[z[basis[[i]]],opKet[[j]]],{i,lenBasis},{j,lenBasis}]
]


(* ::Subsection:: *)
(*1PRDM*)


rdm[state_,spin_,modes_]:= Chop[Table[scalarProduct[state,cdagger[i,spin][c[j,spin][state]]],{i,1,modes},{j,1,modes}]]



(* ::Subsection:: *)
(*number of modes*)


(* ::Text:: *)
(*Grab the number of modes of a state in the z-form: z[{{...},{...}}] (we assume the number of modes for spin-up and spin-down particles is the same).*)


nModes[z[state_]] := Length[state[[1]]]


(* ::Subsection:: *)
(*Convert from the b (bracket) form of a basis state to its z form or vice-versa*)


(* ::Text:: *)
(*Functions to convert from the z-form of a state, z[{{...},{...}}] to the b-form (bracket) of a state, {{...},{...}} where the first bracket gives us the occupation numbers for spins-up and the right for spins-down.*)
(*This obviously only works for basis states and not linear combinations of them. In that case, the z-form must be used.*)


(* ::Subsubsection:: *)
(*From b to z*)


bToz[state_]:=z[state]


(* ::Subsubsection:: *)
(*From z to b*)


zTob[z[state_]]:=state


(* ::Subsection:: *)
(*Convert from the e-form of an arbitrary state to it z-form as a linear combination of basis states and vice-versa*)


(* ::Text:: *)
(*The z-form of a basis state is z[{{...},{...}}], while for a general state it is given as a linear combination of this basis states. For a state having a z-form expansion given by sum{c_i z[i]} it e-form expansion is given by {c_1,...c_N} where N is the number of modes. This is the form we get when we diagonalize an operator whose matrix form was written using the function matrixForm (hence e-form - eigenvalue).*)


(* ::Subsubsection:: *)
(*From e to z*)


eToz[state_,basis_]:=Module[
{len},
len = Length[state];
Sum[Transpose[state][[i]]*z[basis[[i]]],{i,1,len}] (* return *)
]


(* ::Subsubsection:: *)
(*From z to e*)


zToe[state_,basis_]:=Module[
{len,zBasis,basisNewAux,basisNew,rule,nullVector,nullRuleReal,nullRuleComplex},
len = Length[basis];
zBasis =  Table[z[basis[[i]]],{i,1,len}];
basisNewAux = ConstantArray[0,len];
basisNewAux[[1]] = 1;
basisNew = Permutations[basisNewAux];
rule = Table[zBasis[[i]]->basisNew[[i]],{i,1,len}];
(* We require a special rule for the nullVector. When c acts on a state to give zero, the resulting state does not have the form z[{{...},{...}}] 
   but it is simply 0. . In order to use Mathematica's inner product, we need to map this value onto the null vector in N dimensions, 
   N= size of basis for the N particle space. *)
nullVector = ConstantArray[0,len];
nullRuleReal = {0. -> nullVector};
nullRuleComplex = {0. +0.I -> nullVector};
rule = Join[rule,nullRuleReal,nullRuleComplex];

state/.rule (* return *)
]


(* End[] *)


EndPackage[]
