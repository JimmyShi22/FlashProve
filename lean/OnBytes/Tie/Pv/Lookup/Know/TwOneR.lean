-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Know/TwOneR.lean.
The statements on the small lookup's rounds, errors and output, said of the one reduction `o65R` of
OnBytes/Tie/Pv/Lookup/Know/TwOne.lean.

Examples and corollaries that re-word; no new mathematics. The files speak of one chain under three
terms: `A.baseK V VC` (Cb/Pv/Lookup/Know/AsmKV.lean), `A.baseKS (PscLtK.ofShort V VC Ex)`
(OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean) and `A.baseKS (Tw.SK₀ E Ex)`
(Cb/Pv/Lookup/Out/TwFill.lean, at `V₀`, `V₀C`). Here they are one, by rfl; the last step
`postM outA` turns neither the shape nor the errors, by rfl.
Main names:
  `o65R₀ Ex := o65R V₀ V₀C Ex`, `o65Eps₀ Ex`: the reduction and its errors at `V₀`, `V₀C`
    (Cb/G6/Pick.lean).
  `o65_know₀`, `o65_know_sig₀`: `o65_know`, `o65_know_sig` there.
  `o65R_shapeIs`: each of the 65 rounds of `o65R V VC Ex` sends and draws what its entry of
    `TwRound.o65ds` says (`OnBytes.G4.ShapeIs`: three of an entry's numbers).
  `o65R_eps`, `o65R_eps_p`: the list of the errors `o65Eps V VC Ex`, the very term of `o65_know` and
    `o65_know_sig`, is `TwErr.epsN 3 1 3 6` at the size of the field, which is `Cb.Gl.p ^ 3`.
  `o65R_len`: 65 rounds.
  `o65R₀_out`: for all inputs, `o65R₀ Ex` does not refuse, and its value is `o65Out` of the read-out
    of `Tw.chnV`'s last state.
Limits: those of OnBytes/Tie/Pv/Lookup/Know/TwOne.lean. `o65R_shapeIs` counts: it ties sizes, not
which scalar is which, and it ties neither a round's name nor the other eight numbers of an entry
to the shape.

-/
import OnBytes.Tie.Pv.Lookup.Know.TwOne
import OnBytes.Tie.Pv.Lookup.Lists.TwAtO65
import Cb.Pv.Lookup.Out.TwFill

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

section Names
variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
  (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec)

/-- the chain of Cb/Pv/Lookup/Know/AsmKV.lean is that of OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean
-/
example : A.baseK V VC (Ex := Ex) = A.baseKS (PscLtK.ofShort V VC Ex) := rfl
/-- at `V₀`, `V₀C` both are that of Cb/Pv/Lookup/Out/TwFill.lean -/
example : PscLtK.ofShort V₀ V₀C Ex = _root_.Tw.SK₀ E Ex := rfl
example : A.baseK V₀ V₀C (Ex := Ex) = A.baseKS (_root_.Tw.SK₀ E Ex) := rfl
/-- the last step turns neither the shape nor the errors -/
example (kAt : ℕ → A.J ⊕ E) : (oneK A kAt V VC Ex).R.shape = (A.baseK V VC (Ex := Ex)).R.shape :=
    rfl
example (kAt : ℕ → A.J ⊕ E) : (oneK A kAt V VC Ex).e = (A.baseK V VC (Ex := Ex)).e := rfl

end Names

/-- The reduction at `V₀`, `V₀C`. -/
noncomputable def o65R₀ (Ex : ExtSpec) : IOR Unit Ex (List (Row K o65J)) Ex := o65R V₀ V₀C Ex
noncomputable def o65Eps₀ (Ex : ExtSpec) : Err (o65R₀ Ex).shape := o65Eps V₀ V₀C Ex

/-- `o65_know` at `V₀`, `V₀C`. -/
theorem o65_know₀ (Ex : ExtSpec) (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) (m : S.Msg) :
    (o65R₀ Ex).red.Know (jn Ex h.msg fun _ => o65RA).on
      (fun a wp => (jn Ex h.msg fun (_ : Unit) => o65RA).relR a (m, wp))
      (fun b wp => (jn Ex h.msg RBof).relR b (m, wp)) (fun _ _ wp => wp) (o65Eps₀ Ex) :=
  o65_know V₀ V₀C Ex S h m

/-- `o65_know_sig` at `V₀`, `V₀C`. -/
theorem o65_know_sig₀ (Ex : ExtSpec) (S : Sig K) (h : Sig3 S (Fin 15) (Fin 16) (Fin 104)) :
    ((o65R₀ Ex).keep S.Smp S.ext).red.Know (S.over (jn Ex h.msg fun (_ : Unit) => o65RA)).on
      (S.over (jn Ex h.msg fun (_ : Unit) => o65RA)).relR (S.over (jn Ex h.msg RBof)).relR (fun _ _
          w => w)
      (o65Eps₀ Ex) :=
  o65_know_sig V₀ V₀C Ex S h

section AtO65
variable (V : ∀ (Y : PscPar K) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar K) Ex, ShortKC Y Ex) (Ex :
    ExtSpec)

example : (o65R V VC Ex).shape = (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape := rfl
example : o65Eps V VC Ex = (o65A.baseKS (PscLtK.ofShort V VC Ex)).e := rfl
example : (o65R₀ Ex).shape = (o65A.baseKS (_root_.Tw.SK₀ K Ex)).R.shape := rfl

/-- The rounds, for every V, VC. `TwRound.o65ds` is the list of
OnBytes/Tie/Pv/Lookup/Lists/TwAtO65.lean. -/
theorem o65R_shapeIs : OnBytes.G4.ShapeIs K (o65R V VC Ex).shape TwRound.o65ds :=
  TwRound.o65_shape V VC Ex

/-- The errors, for every V, VC: of `errList ε` with ε the theorems' very term: `o65Eps V VC Ex` is
the last argument of `o65_know` and `o65_know_sig` as they are stated. `Fintype.card K` stands in
the list as that term; it is `Cb.Gl.p ^ 3` by `TwRound.o65_card` (`Cb.Gl.gl_card`). -/
theorem o65R_eps : errList (o65Eps V VC Ex) = TwErr.epsN 3 1 3 6 (Fintype.card K) :=
  TwRound.o65_eps V VC Ex
theorem o65R_eps_p : errList (o65Eps V VC Ex) = TwErr.epsN 3 1 3 6 (Cb.Gl.p ^ 3) :=
  TwRound.o65_card ▸ o65R_eps V VC Ex
/-- sixty-five rounds -/
theorem o65R_len : (o65R V VC Ex).shape.length = 65 := TwRound.o65_len V VC Ex

/-- The output at `V₀`, `V₀C`, for all inputs: it never refuses; its value is the last step
`o65Out` on the read-out of the chain's last state as `Tw.chnV` walks it. -/
theorem o65R₀_out (a : Unit × Ex.Str) (τ : Tr (o65R₀ Ex).shape) :
    (o65R₀ Ex).red.out a τ = some (o65Out (o65A.rd (_root_.Tw.chnV (_root_.Tw.SV₀ K Ex) o65A a.1
        τ)), a.2) := by
  have h := _root_.Tw.baseK₀_out Ex o65A a τ
  show ((o65A.baseKS (_root_.Tw.SK₀ K Ex)).R.post (fun x => some (o65Out x)) (ExtMap.id Ex)).red.out
      a τ = _
  rw [_root_.Tw.red_post_out, h]
  rfl

end AtO65
end Cb.Tw
#print axioms Cb.Tw.o65_know₀
#print axioms Cb.Tw.o65_know_sig₀
#print axioms Cb.Tw.o65R_shapeIs
#print axioms Cb.Tw.o65R_eps
#print axioms Cb.Tw.o65R_eps_p
#print axioms Cb.Tw.o65R_len
#print axioms Cb.Tw.o65R₀_out
