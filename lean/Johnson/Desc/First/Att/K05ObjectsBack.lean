-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ObjectsBack.lean: kind K5: THE LOOKUP's ITEM formsT m 2 "objects" RIDES BACK OVER THE KIND's BLOCK: where it holds at the verifier's state after the block it holds at the state in front: the clause "objects" of K5FillRel
(Att/K05Riders.lean).

How. The run "objects" states the rows g.rows of what the verifier has received from the lookup argument, and marks a debt: the kind's block leaves g. The lookup's sharp promise in front (K3LeftOutIs: HeardIs.rows) says of each row RowIs at the ledger in
front: ITS WORTH AT EVERY LATER LEDGER, EVERY MASK ROW AND EVERY FUNCTION OF ENTRIES is one term of the mask row alone (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean). The ledger after the hearing is later. So the row's worth is one at the two states, whatever the
stated function says of the arrays of the second sending there, if it leaves the mask row.

The item formsT m 2 "objects" is TWO sentences: the driver's runs under it are (1, "objects") AND (1, "guests") (Johnson/Desc/First/Borders.lean: runsOf). The second run: the lookup's block is seated with NO
guest (Johnson/Desc/First/Look/K3Own.lean: blockVia seat a.piece laid sent p []): the run returns no claim and hands the state back: its sentence holds outright wherever a ledger is open.

objects_reader · objects_at_link · guests_reader · guests_at_link stand in the light file Johnson/Desc/First/Att/K05ObjectsReaders.lean, which is imported. Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Main names: value_nil · dataQ_part · row_back · formsTQ_objects_back · objects_reader · objects_at_link · guests_reader · guests_at_link · formsTQ_guests · k5FillRel_objects (the clause's text).
PREMISES OF k5FillRel_objects: leftIs (K5AtMg's own field) · hleftQ · hObj (the readers' law at (1, "objects"): objects_at_link pays it at the readers of a link) · hbare (the rows name no entry: the lookups' law on their block's yes) · hIn (under the
  promise the public test formsInT holds at the state in front) · hMask (the stated function leaves the mask row) · hGst (the readers' law at (1, "guests"): guests_at_link pays it) · hTo (the meaning's item gives the sentence at "objects") · hFrom (the two sentences give the item): implications at values.
THE LETTERS UNDER "FOR ALL": hObj: t, F, g: F and g pinned by two equations at t; t free on purpose (a law of the readers' make) · hbare: a' fenced by the promise and "no mark" · hIn: s, y fenced by the promise · hMask, hTo, hFrom: free on purpose (laws of a make).
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Riders
import Johnson.Desc.First.Att.K05FormsKept
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.First.Att.K05JoinHeard
import Johnson.Desc.First.Att.K05JoinThere
import Johnson.Desc.First.Att.K05ReadersGuarded
import Johnson.Desc.First.Att.K05ObjectsReaders
import Johnson.Desc.First.StateLedger
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb.LdLkp (TX)
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt)
open VerifiableInference.Desc.K9 (Readers RunOf readerOf statesOfLink readersOfLink LinkHoles segAt? formsInT lateOf ownRow)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated formsTQ worldOwn dataQ value_eq slotW_ledger Frame strsOf)
open VerifiableInference.Desc.K9L (Bound)

/-- With no late slot the forms' world is the ledger's own, at the data's mask row. -/
theorem value_nil (a : VerifiableInference.Desc.K9.Part) (Dt : Bound GQ) (f : Aff) :
    f.value Reading.gl (worldOwn a [] Dt) = f.value Reading.gl (a.F.worldOf Reading.gl Dt.mask (worldOwn a [] Dt).entry) :=
  value_eq _ _ f (fun _ _ => rfl) fun y _ => slotW_ledger a.F [] _ y.1 rfl

/-- The data off the witness's tables do not hang on the part's ledger. -/
theorem dataQ_part (own : List (ℕ × ℕ)) (s : First.S) (att : First.AttOwn) (rd : ℕ × ℕ → MsgQ) (F F' : Fork) (o o' : Option ℕ) :
    dataQ own (partAt s att F o) rd = dataQ own (partAt s att F' o') rd := by
  unfold dataQ
  rfl

/-- One row: worth 0 at the later ledger gives worth 0 at the earlier one, at one mask row. -/
theorem row_back {F G : Fork} (lt : Fo.Later F G) {row : Aff} {r : TwV.SRow Fo.Pl GQ} (hr : Fo.RowIs Reading.gl F row r)
    (a a' : VerifiableInference.Desc.K9.Part) (haF : a.F = F) (haG : a'.F = G) (Dt Dt' : Bound GQ) (hm : Dt.mask = Dt'.mask)
    (v0 : row.value Reading.gl (worldOwn a' [] Dt') = 0) : row.value Reading.gl (worldOwn a [] Dt) = 0 := by
  rw [value_nil, haG, hr G lt] at v0
  rw [value_nil, haF, hr F (Fo.Later.refl _), hm]
  exact v0

/-- **The sentence rides back.** -/
theorem formsTQ_objects_back (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) {s : First.S} {att : First.AttOwn}
    {xr : Params.AttentionRounds} {rs : List Fmt.RoundView} {hd : Heard} {G : Fork} {g : Forest.Heard} (e : s.here = .att att)
    (hh : hear xr (att.F, rs, 0) = some (hd, G, [], 0)) (hz : Sized att.F)
    (hrows : ∀ i, i < g.rows.size → ∃ r, Fo.RowIs Reading.gl att.F (g.rows.getD i {}) r)
    (hS : Rd.forms 1 "objects" s = some { forms := g.rows.toList, late := [] })
    (hB : Rd.forms 1 "objects" (behind s att hd G) = some { forms := g.rows.toList, late := [] })
    (hIn : formsInT Rd own 1 "objects" s = true) (mS : ∀ Dt, (St.at1 s Dt).mask = Dt.mask)
    (mB : ∀ Dt, (St.at1 (behind s att hd G) Dt).mask = Dt.mask) (rd : ℕ × ℕ → MsgQ)
    (h : formsTQ Rd St own 1 "objects" (behind s att hd G) rd) : formsTQ Rd St own 1 "objects" s rd := by
  obtain ⟨a', R', ha', hR', _, hf'⟩ := h
  obtain rfl : partAt s att G none = a' := Option.some.inj ((segAt_behind (s := s) (a := att) (h := hd) (G := G)).symm.trans ha')
  obtain rfl := Option.some.inj (hB.symm.trans hR')
  obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh hz
  obtain ⟨_, bl⟩ := hear_below hh hz
  have lt : Fo.Later att.F G := ⟨bl.1, bl.ns, fun j hj => by
    obtain ⟨a, b, d⟩ := st j _ _ ⟨hj, rfl, rfl⟩
    exact ⟨a, b, d⟩⟩
  unfold formsInT at hIn
  rw [segAt_front e, hS] at hIn
  have hIn2 := (Bool.and_eq_true_iff.1 hIn).2
  refine ⟨_, _, segAt_front e, hS, rfl, fun f hf => ⟨List.all_eq_true.1 hIn2 f hf, ?_⟩⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < g.rows.size := by simpa using hi
  have ef : g.rows.toList[i] = g.rows.getD i {} := by
    simp [Array.getD, hi']
  obtain ⟨r, hr⟩ := hrows i hi'
  rw [ef]
  refine row_back lt hr (partAt s att att.F (VerifiableInference.Desc.K9.owedOf s)) (partAt s att G none) rfl rfl _ _
    ((mS _).trans ((congrArg (·.mask) (dataQ_part own s att rd att.F G _ none)).trans (mB _).symm)) ?_
  rw [← ef]
  exact (hf' _ hf).2

/-- Where the reader answers with no form the sentence holds outright. -/
theorem formsTQ_guests (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) {s : First.S} {att : First.AttOwn} (e : s.here = .att att)
    (hG : Rd.forms 1 "guests" s = some { forms := [], late := [] }) (rd : ℕ × ℕ → MsgQ) : formsTQ Rd St own 1 "guests" s rd :=
  ⟨_, _, segAt_front e, hG, rfl, fun _ hf => absurd hf (List.not_mem_nil)⟩

/-- **The clause "objects" of K5FillRel.** -/
theorem k5FillRel_objects {Pp W Cl St₀ J₀ : Type} [DecidableEq J₀] {Fr : Frame} (claim : Aff → Cl) (Mg : Meaning Pp W) (N : Numbers)
    (links : List ModelPart) (π : Pp) (base m : ℕ) (pl : Place) (O : List Item) (Q : List Pub) (own : Params.AttentionRounds)
    (hs : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀) (Qr : Fork → Prop)
    (x0 : First.S × Fr.E.Str → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (leftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        hs lm first ι Qr (x0 a') (gOf a') a'.1)
    (hleftQ : Pub.left m ∈ Q) (Rd : Readers) (St : Stated) (ownL : List (ℕ × ℕ)) (rdOf : W → ℕ × ℕ → MsgQ)
    (hObj : ∀ (t : First.S) (F : Fork) (g : Forest.Heard), t.fork? = some F → t.lookHeard? = some g →
      (∀ f ∈ g.rows.toList, f.ents = #[]) → Rd.forms 1 "objects" t = some { forms := g.rows.toList, late := [] })
    (hbare : ∀ a' : First.S × Fr.E.Str, onT N Mg links π Fr pl O Q a' → ∀ f ∈ (gOf a').rows.toList, f.ents = #[])
    (hIn : ∀ s y, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      formsInT Rd ownL 1 "objects" s = true)
    (hMask : ∀ t Dt, (St.at1 t Dt).mask = Dt.mask)
    (hTo : ∀ t y w, Mg.formsT m 2 "objects" (π, t) y w → formsTQ Rd St ownL 1 "objects" t (rdOf w))
    (hGst : ∀ (t : First.S) (F : Fork), t.fork? = some F → Rd.forms 1 "guests" t = some { forms := [], late := [] })
    (hFrom : ∀ t y w, formsTQ Rd St ownL 1 "objects" t (rdOf w) → formsTQ Rd St ownL 1 "guests" t (rdOf w) →
      Mg.formsT m 2 "objects" (π, t) y w) :
    ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      Mg.formsT m 2 "objects" (π, behind s att hd G) (strsOf Fr y') w → Mg.formsT m 2 "objects" (π, s) (strsOf Fr y) w := by
  intro s att hd G rs y y' w hon hm e hh _ hT
  have hP := onAt_pubP hon hm _ hleftQ
  obtain ⟨F, F', rs₀, _, _, L, e1, e2, _⟩ := leftIs (s, y) hP
  have e1' : s.lookHeard? = some (gOf (s, y)) := e1
  obtain rfl : F' = att.F := Option.some.inj ((show s.fork? = some F' from e2).symm.trans (fork_front e))
  have hlk : (behind s att hd G).lookHeard? = some (gOf (s, y)) := by
    unfold First.S.lookHeard? at e1' ⊢
    rw [e] at e1'
    exact e1'
  have hb := hbare (s, y) ⟨hon, hm⟩
  exact hFrom s _ w (formsTQ_objects_back Rd St ownL e hh ⟨L.padLeft.fit.1, L.padLeft.fit.2.1, L.padLeft.fit.2.2⟩
    (fun i hi => ⟨_, L.heardIs.rows i hi⟩) (hObj s att.F _ (fork_front e) e1' hb) (hObj _ G _ rfl hlk hb) (hIn s y hon hm)
    (hMask s) (hMask _) (rdOf w) (hTo _ _ w hT)) (formsTQ_guests Rd St ownL e (hGst s att.F (fork_front e)) (rdOf w))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.value_nil
#print axioms VerifiableInference.Desc.First.Att.P.formsTQ_objects_back
#print axioms VerifiableInference.Desc.First.Att.P.formsTQ_guests
#print axioms VerifiableInference.Desc.First.Att.P.k5FillRel_objects
