-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05PlanesWorth.lean: kind K5: THE PREMISES hz AND h4 OF THE ROW
K05_host_planes (Johnson/Desc/First/Att/K05HostPlanes.lean: kind K5 pays the
table of joints' item worth "planes" of an attention segment's lookup on the calls): "the claims of
the lookup's run on the planes are worth 0 in the stated world of a later ledger", FROM THE TABLE's
OWN SENTENCE formsTQ ON THAT RUN: the kind's carriage between the two worlds, once more, at a fourth
run: it is general in the list of forms and in the run's name.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A CARRIAGE, NO PAYMENT.

EVERY LETTER UNDER ∀ THAT THE CONCLUSION READS, AND WHAT PINS IT: i, K: the seat's reading's answer
at the record sP (an equation) · f: a member of fs. All else are letters of the theorem.

Main names:
  `funsAt_of_inOf`: where the claims' seat's reading answers (i, K) at a record, funsAt A is the
    law's list of tables at i.
  `cells_are_nu`: the planes' matrix of matsOfMsg at the witness's messages is the lookup's places
    at the cells: h4 at M := matsOfMsg …: by the two texts.
  `hz_of_formsT`: **hz**: at every answer (i, K) of the seat's reading at sP with K the plan's
    width: every form of fs is worth 0 in H.worldOf (the lookup's places at the masks) (entryOf … K
    (matsOfMsg …) (oldOf A.S gL i).t.funs.toList). FROM: the sentence formsTQ Rd St own piece run sP
    · the reader's answer R, whose list holds fs · LateLaid pt.F R.late H fs
    (Johnson/Desc/First/Att/K05WorthLate.lean: under every named slot the table's hidden value is
    H's own: the law lateLaid_affInT (Keep/LateLaidAt.lean) at H := the ledger behind the run) ·
    TieFacts at sP and fs (K05WorldTieAt.lean: its clause ents: every entry of fs names row 0 of
    A.iU3) · the public premises of worldTie_at · StatedAtt at sP · hi ≤ x.ns.
  `width_of_inOf`: the width that the seat's reading answers is the ledger's array's. `hz_at`: **hz
    in the row's own form**: over a list of claims clP and their forms, at EVERY answer (i, K): the
    width comes of U3At at sP's ledger.
Limits. A rule over letters. gL is read by no term of the conclusion but through oldOf's tables,
which do not hang on it. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorldTieAt
import Johnson.Desc.First.Att.K05WorthLate
import Johnson.Desc.First.Att.K05PlacesNu
import Johnson.Desc.First.Att.Claims.FunsAt
import Johnson.Desc.First.Att.K05EntsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (GQ Stated Mem seatTab msgsOf MsgT formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu)
open K5Law (entryOf oldOf funsAt AllZero inOf_isAt inAt_parts)

/-- Where the seat's reading answers, funsAt is the law's list of tables at the answer. -/
theorem funsAt_of_inOf (A : Attention.Plan) {s : First.S} {i : Runs.In} {K : ℕ}
    (h : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, K)) (gL : Forest.Heard) :
    funsAt A s = (oldOf A.S gL i).t.funs.toList := by
  unfold funsAt
  rw [h]
  rfl

/-- The width that the seat's reading answers is the ledger's array's. -/
theorem width_of_inOf (A : Attention.Plan) {s : First.S} {a₀ : First.AttOwn} {i : Runs.In} {K Kc : ℕ}
    (hs : s.here = .att a₀) (hU : U3At A Kc a₀.F)
    (h : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, K)) : K = Kc := by
  rw [inOf_isAt hs] at h
  obtain ⟨g, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hh, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, hk, _⟩ := inAt_parts h
  obtain ⟨T, hT, hK, _⟩ := hU
  have hT' : a₀.F.trees[(parCOf A).iU3]? = some T := hT
  rw [hT'] at hk
  exact (Option.some.inj hk).symm.trans hK

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **h4 at M := matsOfMsg at the witness's messages.** -/
theorem cells_are_nu (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (w : Wit Cells Tok MsgT) (r c : ℕ) :
    matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w) (A.S.cf.NAs + 2) r c =
      attNu x A.S A.seam.tl D rad seat arr w (.cell r c) := rfl

include Ex Wp α in
/-- **hz: the forms' worth in the stated world of a later ledger.** (Ex, Wp, α, ns and N are read by
no term of the statement: the proof goes through the law's reading of the mask row, which bears
them.) -/
theorem hz_of_formsT (ns : ℕ) (N : Nums) (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ))
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (w : Wit Cells Tok MsgT) (piece : ℕ) (run : String) (fs : List Aff) (hi : ℕ)
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) {sP : First.S}
    {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx} {R : VerifiableInference.Desc.K9.Read}
    (H : Fork) (gL : Forest.Heard)
    (q : formsTQ Rd St own piece run sP (seatTab D.codes arr ms w))
    (hRr : Rd.forms piece run sP = some R) (hsub : ∀ f ∈ fs, f ∈ R.forms)
    (hl : LateLaid pt.F R.late H fs)
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true) (hhi : hi ≤ x.ns)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : StatedAtt St A (funsAt A) sP) (T : TieFacts x A D rad own ps qs hi sP L pt fs) :
    ∀ (i : Runs.In) (K : ℕ), inOf (seatCO (parCOf A)) (parCOf A) sP = some (i, K) → K = plannedK A →
      ∀ f ∈ fs, f.value Reading.gl
        (H.worldOf Reading.gl (fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
          (entryOf Reading.gl A.seam.tl K
            (matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w))
            (oldOf A.S gL i).t.funs.toList)) = 0 := by
  intro i K hin hK
  subst hK
  have hslots := fun f hf => slots_below q T.hpt hRr f (hsub f hf)
  have W := worldTie_at x A D rad Ex Wp α ns N St own arr seat ms w fs hi ps qs (funsAt A) _ hR hmk
    hone hm hcov hcovM hSt T hslots (funsAt_of_inOf A hin gL)
  have W' := W.mask_to (mask' := fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
    fun f hf y hy => mask_is_nu x A.S A.seam.tl D rad seat arr Ex Wp α ns N w y.1
      (Nat.lt_of_lt_of_le (hslots f hf y hy) (Nat.le_trans T.hns hhi))
  exact worth_of_formsTQ_late Rd St own piece run sP _ q T.hpt hRr H _ _ fs hsub hl W'

include Ex Wp α in
/-- **hz, in the row's own form**: over the claims of a list clP, at every answer of the seat's
reading. -/
theorem hz_at {Cl : Type} (form : Cl → Aff) (clP : List Cl) (ns : ℕ) (N : Nums) (Rd : Readers)
    (St : Stated) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (w : Wit Cells Tok MsgT) (piece : ℕ) (run : String) (hi : ℕ)
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) {sP : First.S} {a₀ : First.AttOwn}
    {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx} {R : VerifiableInference.Desc.K9.Read}
    (H : Fork) (gL : Forest.Heard) (hs : sP.here = .att a₀) (hU : U3At A (plannedK A) a₀.F)
    (q : formsTQ Rd St own piece run sP (seatTab D.codes arr ms w))
    (hRr : Rd.forms piece run sP = some R) (hsub : ∀ y ∈ clP, form y ∈ R.forms)
    (hl : LateLaid pt.F R.late H (clP.map form))
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true) (hhi : hi ≤ x.ns)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl (clP.map form)) D x.link k.val →
      MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl (clP.map form)) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : StatedAtt St A (funsAt A) sP)
    (T : TieFacts x A D rad own ps qs hi sP L pt (clP.map form)) :
    ∀ (i : Runs.In) (K : ℕ), inOf (seatCO (parCOf A)) (parCOf A) sP = some (i, K) →
      ∀ y ∈ clP, (form y).value Reading.gl
        (H.worldOf Reading.gl (fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
          (entryOf Reading.gl A.seam.tl K
            (matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w))
            (oldOf A.S gL i).t.funs.toList)) = 0 :=
  fun i K hin y hy =>
    hz_of_formsT x A D rad Ex Wp α ns N Rd St own arr seat ms w piece run (clP.map form) hi ps qs H gL
      q hRr (fun f hf => by
        obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hf
        exact hsub y' hy') hl hR hmk hhi hone hm hcov hcovM hSt T i K hin
      (width_of_inOf A hs hU hin) (form y) (List.mem_map.2 ⟨y, hy, rfl⟩)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.funsAt_of_inOf
#print axioms VerifiableInference.Desc.First.Att.P.cells_are_nu
#print axioms VerifiableInference.Desc.First.Att.P.width_of_inOf
#print axioms VerifiableInference.Desc.First.Att.P.hz_of_formsT
#print axioms VerifiableInference.Desc.First.Att.P.hz_at
