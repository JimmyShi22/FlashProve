-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartReqCtb.lean: bookkeeping for the object: the shapes of the fourth part (a
request with one segment: Cb/Obj/LdObjectReqStd.lean, Cb/Obj/LdObjectPartReq.lean) are countable,
under the hypotheses named below.

Countability is bookkeeping for the passage to one random oracle (the head of
Cb/Obj/LdObjectCtb.lean).
Statements are the theorems' own texts; proofs by the rules of Cb/Obj/LdObjectCtb*.lean. A shape is
countable (`CtbSh`, CompileK/ImplCountable.lean) if positions, symbols and plain parts of every
round are countable.

Main names:
  `ctb_sum`: the fold of a stage (Cb/Ld/LdSum.lean): asked: a native symbol of the fresh mask's code
    has finitely many coordinates.
  `ctb_gLink`: bridge, arrangement, fold, beside the carried part (`GHeld.link`,
    Cb/Ld/LdGroupSeg.lean): the same, for non-empty `G.P` and if every oracle message is a member of
    the group or kept (`hc`).
  `rqReq_ctb`: the request with one segment: asked, for non-empty P: the symbols of the first
    sending's family and of the one sending's family are countable (`h₁`, `h₂`); its link l is
    countable (`hl`).
  `rqPart_ctbR`: so the fourth part's clause (`PReq.CtbR`, Cb/Obj/LdObjectCtbSplit.lean), for
    non-empty P and if every oracle message that is kept at the bridge is held and the rows are
    finitely many (`IsEmpty S₂.O`, `Fintype (rqClose ..).loc.RowN`, as `rqPart` asks), from: native
    symbols of the base code, of the mask code and of the new messages' codes have finitely many
    coordinates.



Limits: on a protocol this file has two kinds of conclusion: countability (as in `rqReq_ctb`,
`rqPart_ctbR`) and, of the toy's code `LdToy74.toyLd74 R`, `LdCode.FinNS`
(`finNS_toy74x`); beyond these kinds no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartReqToy
import Cb.Obj.LdObjectCtbSplit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E : Type} [Field E] [Fintype E]

theorem ctb_sRounds (Ch : Type) [Fintype Ch] [Nonempty Ch] (n : ℕ) :
    ∀ k, CtbSh (List.replicate k (sRound E Ch n))
  | 0 => trivial
  | k + 1 =>
    ⟨⟨inferInstanceAs (Countable Empty),
        fun p => p.elim,
        inferInstanceAs (Countable (Fin (n + 1) → E))⟩,
      ctb_sRounds Ch n k⟩

/-- The fold of a stage. -/
theorem ctb_sum {P : Type} [Fintype P] (Y : SumPar E P) (h : Y.Cw.FinNS) : CtbSh Y.ior.shape :=
  ⟨⟨inferInstanceAs (Countable Y.Cw.NP), fun p => by
      haveI := h p
      exact inferInstanceAs (Countable (Y.Cw.NS p → E)), inferInstanceAs (Countable E)⟩, ctb_sRounds Y.Ch Y.n Y.k⟩

/-- Bridge, arrangement, fold, beside the carried part. -/
theorem ctb_gLink {B Kc St₀ Wp : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
    {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
    (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp)
    (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ) (h : Sh.par.Cw.FinNS) :
    (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).Ctb := by
  show CtbSh
    ((ldBridge G kp Sb Z St₀ E₀).shape ++
      ([] ++ ([] ++ (Sh.par.reform (Sh.form Sb sl Z)).ior.shape)))
  exact ctbSh_append (ctb_plain Unit Z.D () trivial) (ctb_sum (Sh.par.reform (Sh.form Sb sl Z)) h)

end

section
variable {F E P Pn : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype P]
  [Nonempty P] [Fintype Pn] (Cf : LdCf F E) (R : StdGM E P) (T : StdArr R.D) (kp : R.A → Prop)
  [DecidablePred kp] (Hh : StdHeld T kp) (V : StdNew Hh.hd Pn)
  (w1 : (rqFold Cf.conf R T kp Hh).tgt.S.Wit × (rqFold Cf.conf R T kp Hh).tgt.Wp) (L₂ t₂ tl : ℕ)
  (En : RqEnd Cf (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc) (w0 : (rqA (E := E) Cf.conf).W)
  (L₁ t₁ : ℕ) (l : Link Unit (rqFold Cf.conf R T kp Hh).src.J (rqFold Cf.conf R T kp Hh).mid)
  (c0 : Cf.conf.Cells)

/-- The request with one segment. -/
theorem rqReq_ctb (h₁ : (rqFirst Cf.conf R w0 L₁ t₁).N.CtbSy)
    (h₂ : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).snd.N.CtbSy) (hl : l.Ctb) :
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ l c0).Ctb where
  first := h₁
  more := (LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩
  segs := by
    show LdSegs.Ctb (.snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l))
    rw [LdSegs.Ctb, LdSegs.Ctb]
    exact ⟨trivial, ⟨LdProg.ctb_nil _, (LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, hl⟩, h₂⟩⟩
  last := (LdProg.ctb_snoc _ _).2 ⟨LdProg.ctb_nil _, trivial⟩

variable (B0 : StdLn Cf Pn) (tb₃ t : ℕ) (dw : R.D.S.Wit × (Cf.conf.PIdx × Cf.conf.Cells)) (d : ℕ)
  (Lst mC mS mW : ℕ → ℕ) (L : ℕ) (w₀ : Cf.conf.PIdx × Cf.conf.Cells)
  [IsEmpty (rqFold Cf.conf R T kp Hh).S₂.O] [Fintype (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.RowN]
  [Nonempty Pn] [Nonempty (Fin Cf.C₀.n)]

omit [Nonempty Pn] [Nonempty (Fin Cf.C₀.n)] in
/-- The fourth part's clause. -/
theorem rqPart_ctbR (hC : R.Cb.FinNS) (hZ : R.Zb.FinNS)
    (hc : V.Mc.Cm.FinNS) (hn : ∀ k, (V.Mn k).Cm.FinNS) :
    (rqPart Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃ t dw d Lst mC mS mW L w0 L₁ t₁ c0 w₀).CtbR := by
  refine pReq_ctbR _ (rqReq_ctb Cf R T kp Hh V w1 L₂ t₂ tl _ w0 L₁ t₁ _ c0 ?_ ?_ ?_)
  · intro a p
    haveI := finNS_pair _ _ (finNS_il R.Cb (R.Rm a) hC) (finNS_il R.Zb (R.Rz a) hZ) p
    exact inferInstanceAs (Countable (((R.Cb.il (R.Rm a)).pair (R.Zb.il (R.Rz a))).NS p → E))
  · intro a p
    match a, p with
    | none, p =>
      haveI := hc p
      exact inferInstanceAs (Countable (V.Mc.Cm.NS p → E))
    | some k, p =>
      haveI := hn k p
      exact inferInstanceAs (Countable ((V.Mn k).Cm.NS p → E))
  · exact ctb_gLink Hh.hd noSb (noSl E _) (rqZ R) (reqOver Cf.conf ((R.D.S.sub kp).Msg))
      _ dw d t Lst mC mS mW L (finNS_il T.sh.par.Zw _ hZ)

end

/-- The same as `finNS_toy74`, with the instances as plain arguments (for rows whose instances are
not found by the search). -/
theorem finNS_toy74x (R : Type) (i₁ : Fintype R) (i₂ : DecidableEq R) :
    (@LdToy74.toyLd74 R i₁ i₂).FinNS :=
  @finNS_toy74 R i₁ i₂

open LdToy LdToy7 LdToy74 LdGToy

end Cb
