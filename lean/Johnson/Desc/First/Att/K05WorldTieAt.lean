-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05WorldTieAt.lean: kind K5: THE PREMISE hTie OF billsWorthJ_of_formsT
(Johnson/Desc/First/Att/K05WorthAtTable.lean), TO THE LETTER, AT THE WITNESS OF THE RULE OF
COMPOSITION AND AT THE STATED FUNCTION OF AN ATTENTION SEGMENT: the table of joints' world and the
law's own world agree at the slots and entries that the returned forms name.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. No premise is evaluated at a plan or a record. D : Sent IS
BUILT NOWHERE in this library.

Main names:
  `uAtt A fA`: **the stated function of the array of the reads at an attention segment**, in the
    type of the letter u of Stated.of (Johnson/Desc/Sound/FormsT.lean): row r,
    place i ↦ entryOf (Johnson/Desc/First/Att/Claims/TabsByChoice.lean) at the plan's record of the
    smallness test and planned number of columns, at the matrices off the data (matsOfData,
    Johnson/Desc/First/Att/K05DataMats.lean), at the list of tables fA s: A LETTER: meant: the
    tables of the claims' seat's own reading at the record. Noncomputable: entryOf picks a table by
    choice.
  (In hTie_at StatedAtt is asked AT THE RECORDS OF THE SEGMENT ITSELF, those whose open link has the
    place's number, AND AT NO OTHER: one St serves all segments: asked at every record it could be
    met by a St made for this segment alone.)
  `StatedAtt St A fA s`: what is asked of the letter St at the record s: it leaves the mask row; at
    a cell of an array of the open segment's second sending it is uAtt A fA. `statedAtt_of`:
    Stated.of (uAtt A fA) meets it, at every record.
  `TieFacts … s L pt fs`: THE RECORD's SIDE, AS ONE BUNDLE: the premises on the record of addrTie_at
    (Johnson/Desc/First/Att/K05AddrTieAt.lean: three Bools, four equations, hok, the part and the
    link); the ledger has at most hi slots; and three on the entries: the link's list names an array
    at A.iU3; it is of the second sending; every entry of the forms names row 0 of A.iU3.
  `slots_below`: every slot that a form of the table's sentence formsTQ names lies below the
    ledger's number of slots: by the sentence's own test (slotIn): so addrTie_at's hslots is paid in
    hTie_at.
  `worldTie_at`: WorldTie at one record.
  `hTie_at`: **hTie, to the letter.**
WHO PAYS WHAT. The public five and the record's side: on the face of K05AddrTieAt.lean. (sec),
(there), (ents): other files on the array of the reads, under premises of
their own; not joined. "Under Returns fA at the record behind the lay is the law's list of tables":
paid at fA := the tables of the claims' seat's own reading (funsAt) in
Johnson/Desc/First/Att/K05WorthAtFuns.lean, where it leans on "in front of the lay the open
segment's own field g is what the lookup has heard", which NOBODY pays. The premise hk of addrTie_at
is paid here (kept_born, Johnson/Desc/First/Att/K05KeptBorn.lean).
Limits. A rule over letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AddrTieAt
import Johnson.Desc.First.Att.K05PublicB
import Johnson.Desc.First.Att.K05KeptBorn
import Johnson.Desc.Sound.FormsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.K9 (Readers affInT slotIn)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated Mem seatTab msgsOf MsgT dataQ second of_mask of_second
  formsTQ)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt sigListCalls seatCalls keptAt bornAt)
open K5Law (entryOf oldOf)

/-- **The stated function of the array of the reads at an attention segment.** -/
noncomputable def uAtt (A : Attention.Plan) (fA : First.S → List HFun) :
    First.S → Bound GQ → ℕ × String → ℕ → ℕ → GQ :=
  fun s Dt _ r i =>
    entryOf Reading.gl A.seam.tl (plannedK A)
      (matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) Dt) (fA s) 0 r i

/-- What is asked of the letter St at a record of an attention segment. -/
structure StatedAtt (St : Stated) (A : Attention.Plan) (fA : First.S → List HFun) (s : First.S) :
    Prop where
  mask : ∀ Dt : Bound GQ, (St.at1 s Dt).mask = Dt.mask
  cell : ∀ (Dt : Bound GQ) (c : ℕ × String) (r i : ℕ), second s c = true →
    (St.at1 s Dt).cell c.1 c.2 r i = uAtt A fA s Dt c r i

theorem statedAtt_of (A : Attention.Plan) (fA : First.S → List HFun) (s : First.S) :
    StatedAtt (Stated.of (uAtt A fA)) A fA s :=
  ⟨fun Dt => of_mask _ s Dt, fun Dt c r i h => of_second _ s Dt c r i h⟩

/-- **The record's side, as one bundle.** -/
structure TieFacts (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan) (D : Sent)
    (rad : OracleShape → Nat) (own : List (ℕ × ℕ))
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (hi : ℕ) (s : First.S) (L : LinkCtx)
    (pt : VerifiableInference.Desc.K9.Part) (fs : List Aff) : Prop where
  hB1 : liveReqB (bornAt D x.link) s = true
  hB2 : seatsOnB (keptAt D x.link).length ps own s = true
  hB3 : shapesOnB (keptAt D x.link).length qs s = true
  hlink : L.link = x.link
  hshape : L.check.frame.shape = D.shape
  hlay : L.check.rows.layout = D.layout
  harr : L.arrayOf = D.arrayOf.getD x.link #[]
  hok : LaidOkAt x A.seam.tl D L.check.frame s.st
  hpt : segAt? s = some pt
  hL : s.link? = some L
  hns : pt.F.ns ≤ hi
  there : (L.arrayOf[A.iU3]?).isSome = true
  sec : ∀ b, L.arrayOf[A.iU3]? = some b → second s b = true
  ents : ∀ f ∈ fs, ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0

/-- **Every slot that a form of the table's sentence names lies below the ledger's number of
slots**: by the sentence's own test. -/
theorem slots_below {Rd : Readers} {St : Stated} {own : List (ℕ × ℕ)} {piece : ℕ} {run : String}
    {s : First.S} {rd : ℕ × ℕ → MsgQ} (h : formsTQ Rd St own piece run s rd)
    {pt : VerifiableInference.Desc.K9.Part} (hpt : segAt? s = some pt)
    {R : VerifiableInference.Desc.K9.Read} (hR : Rd.forms piece run s = some R) :
    ∀ f ∈ R.forms, ∀ y ∈ f.slots.toList, y.1 < pt.F.ns := by
  obtain ⟨a', R', ha', hR', _, hf⟩ := h
  obtain rfl : a' = pt := Option.some.inj (ha'.symm.trans hpt)
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  intro f hm y hy
  have h1 := (hf f hm).1
  unfold affInT at h1
  obtain ⟨_, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h1
  have h3 := List.all_eq_true.1 h2 y hy
  unfold slotIn at h3
  obtain ⟨h4, _⟩ := Eq.mp (Bool.and_eq_true _ _) h3
  exact of_decide_eq_true h4

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **WorldTie at one record.** -/
theorem worldTie_at (ns : ℕ) (N : Nums) (St : Stated) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (w : Wit Cells Tok MsgT) (fs : List Aff) (hi : ℕ) (ps : List (ℕ × (ℕ × ℕ)))
    (qs : List (ℕ × OracleShape)) {s : First.S}
    {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx} (fA : First.S → List HFun)
    (funs : List HFun)
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : StatedAtt St A fA s) (T : TieFacts x A D rad own ps qs hi s L pt fs)
    (hslots : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, y.1 < pt.F.ns) (hfuns : fA s = funs) :
    WorldTie St own s pt (seatTab D.codes arr ms w)
      ((attLin x A.S A.seam.tl D rad Ex Wp α ns N).maskOf
        (msgsOf D.codes (sigListCalls D rad x.link) seat arr w))
      (entryOf Reading.gl A.seam.tl (plannedK A)
        (matsOfMsg x A.seam.tl D rad (msgsOf D.codes (sigListCalls D rad x.link) seat arr w)) funs)
      fs := by
  obtain ⟨e1, _, _⟩ := seg_parts T.hpt T.hL
  refine worldTie_of_addrTie x A.seam.tl D rad Ex Wp α A.S ns N St own s pt _ _ A.iU3 (plannedK A)
    funs fs
    (addrTie_at x A.seam.tl D rad own arr seat ms w fs hi ps qs hR hmk (kept_born D x.link) hone
      hm T.hB1 hcov hcovM T.hB2 T.hB3
      T.hlink T.hshape T.hlay T.harr T.hok T.hpt T.hL
      fun f hf y hy => Nat.lt_of_lt_of_le (hslots f hf y hy) T.hns)
    (fun j => by rw [hSt.mask]) (fun b hb i => ?_) (by rw [e1]; exact T.there) T.ents
  rw [e1] at hb
  rw [hSt.cell _ b 0 i (T.sec b hb)]
  unfold uAtt
  rw [T.hL, hfuns, e1]
  rfl

/-- **hTie, to the letter.** -/
theorem hTie_at {Y : Type} (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds)
    (on : First.S × Y → Prop)
    (R' : First.S × Y → Wit Cells Tok MsgT → Prop) (Rd : Readers) (St : Stated)
    (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (fA : First.S → List HFun)
    (hR : SymsOK x A.seam.tl D rad)
    (hmk : masksUpTo D x hi = true)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link → StatedAtt St A fA s)
    (hR' : ∀ b w, R' b w → formsTQ Rd St own 2 "first" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "second" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "join" b.1 (seatTab D.codes arr ms w))
    (hRd : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          Rd.forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          Rd.forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          Rd.forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hrec : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ pt : VerifiableInference.Desc.K9.Part, segAt? b.1 = some pt →
          (∃ L, TieFacts x A D rad own ps qs hi b.1 L pt (l₁ ++ l₂ ++ [xj.1])) ∧
            fA b.1 = (oldOf A.S (gOf a) i).t.funs.toList) :
    ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ pt : VerifiableInference.Desc.K9.Part, segAt? b.1 = some pt →
          WorldTie St own b.1 pt (seatTab D.codes arr ms w)
            ((attLin x A.S A.seam.tl D rad Ex Wp α ns N).maskOf
              (msgsOf D.codes (sigListCalls D rad x.link) seat arr w))
            (entryOf Reading.gl A.seam.tl (plannedK A)
              (matsOfMsg x A.seam.tl D rad (msgsOf D.codes (sigListCalls D rad x.link) seat arr w))
              (oldOf A.S (gOf a) i).t.funs.toList) (l₁ ++ l₂ ++ [xj.1]) := by
  intro a b w ha hRw F G h Ls h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt pt hpt
  obtain ⟨⟨L, T⟩, hf⟩ := hrec a b w ha hRw F G h Ls h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt pt hpt
  obtain ⟨R₁, R₂, R₃, e1, _, m1, e2, _, m2, e3, _, m3⟩ :=
    hRd a b w ha hRw F G h Ls h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt
  obtain ⟨q1, q2, q3⟩ := hR' b w hRw
  obtain ⟨att, _, _, eb⟩ := lay_is h1 h2
  have hhere : b.1.here = .att { att with F := G, heard5 := some h } := by
    rw [eb]
    rfl
  have eL : att.L = L := by
    have := T.hL
    unfold First.S.link? at this
    rw [hhere] at this
    exact Option.some.inj this
  have hfl : att.L.check.frame.link = x.link := by
    rw [eL]
    exact (liveReqB_at T.hB1 T.hL).1.trans T.hlink
  refine worldTie_at x A D rad Ex Wp α ns N St own arr seat ms w _ hi ps qs fA _ hR hmk hone (hm _)
    (hcov _) hcovM (hSt _ _ hhere hfl) T (fun f hf' y hy => ?_) hf
  rcases List.mem_append.1 hf' with hf' | hf'
  · rcases List.mem_append.1 hf' with hf' | hf'
    · exact slots_below q1 hpt e1 f (m1 f hf') y hy
    · exact slots_below q2 hpt e2 f (m2 f hf') y hy
  · rw [List.mem_singleton.1 hf'] at hy
    exact slots_below q3 hpt e3 _ m3 y hy

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.statedAtt_of
#print axioms VerifiableInference.Desc.First.Att.P.slots_below
#print axioms VerifiableInference.Desc.First.Att.P.worldTie_at
#print axioms VerifiableInference.Desc.First.Att.P.hTie_at
