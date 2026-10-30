-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptFactsOf.lean: the code switch: PinKeptJoin.lean's
KeptFacts, AS FAR AS THE SWITCH's OWN SIDE PAYS IT. OF ITS SIXTEEN FIELDS: SIX ARE DERIVED HERE
(rows · bits · pad · fit · reads · fits), AND THREE OF THE FOUR CLAUSES OF A SEVENTH (new); FIVE ARE
HANDED THROUGH from premises on the switch's side (at' · one · st · msg · stored); FOUR, AND new's
FOURTH CLAUSE, STAY PREMISES ON THE TABLE's SIDE (seatIs · listed · num · shown · «one number»).
  entry_shape  the frame's entry for a kept member has the typed shape's main rows, row bits and
               pad, where the front's statement has a message of that shape at the entry's own
               number. By kept_rec (Johnson/Top/H/SwitchKeptRec.lean) and the library's stSent_old
  new_copy     the new copy's shape has the old one's main rows and row length, its pad stands where
               the old one's stood, and the rows are long enough for the pad. By check_kept,
               padRaw_same and fit_of_pad (Johnson/Top/H/SwitchFront.lean)
  stored_facts  the member's first stored sample row: its form reads as its coefficients
               (K2Hands/FormOnReads.lean's stored_reads), and a typed seed fits it. By
               stored_of_goodS and seedFits_of_stored (Johnson/Top/H/SwitchSeedFits.lean)
               keptFacts_of THE STATEMENT: KeptFacts at the frame's own entry
THE PREMISES OF keptFacts_of. (1) ON THE SWITCH's SIDE: the front's frame · the program's test on
the public sizes · the front's codes are the typed ones · SampleGoodS · Fit · five facts in the
form in which, BY THEIR HEADS, numAt_inj | hmem_of | hrb_of | hx_of | shape_of conclude
(Johnson/G/SwitchSampleTop.lean: not imported: it stands over a file of tests by Lean's kernel) ·
hst: the state's statement has the front's statement's oracle messages · hT: the
typed new list has the target's kept shape at the member's place: MEANT to come from «the notices
are the typed list»: NO LEMMA IN THIS FORM IS KNOWN HERE. (2) ON THE TABLE's SIDE: KeptSeat ·
the seat is one of the plan's list · its number there is the entry's own · arr gives the two
copies one number (no payer is named) · every leaf is shown (the table's promise).
LIMITS. An assembly. None of the premises is shown at a real value here. pinKept IS NOT PAID. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.PinKeptJoin
import Johnson.Top.H.SwitchSeedFits
import Johnson.Top.H0.K2Hands.FormOnReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (ShownAt numAt)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK}

/-- **The frame's entry for a kept member has the typed shape's numbers.** -/
theorem entry_shape (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (hW : K2.frameAt fx = some W₀)
    (hcs : fx.st.codes = r.cs) (a : ℕ) (kk : KeptPlace) (hat : W₀.kept[a]? = some kk)
    (xo : OnBytes.Oracle) (hmsg : fx.st.oracles[kk.old]? = some xo) (so : OracleShape)
    (hsh : xo.shape = so) :
    kk.rows = so.mainRows ∧ kk.rowBits = ceilLog2 so.mainRows ∧ kk.pad = padPlaces r.cs so ∧
      ∃ hi : a < (switchKept fx.f.rows).size, kk.old = (switchKept fx.f.rows)[a] ∧
        ((K2.skelOf fx).oracles.getD (switchKept fx.f.rows)[a] default).shape = so := by
  obtain ⟨hi, e1, e2, e3, e4⟩ := kept_rec _ _ _ _ _ W₀ hW a kk hat
  have hlt : kk.old < fx.st.oracles.size := (Array.getElem?_eq_some_iff.1 hmsg).1
  have eo : (K2.skelOf fx).oracles.getD (switchKept fx.f.rows)[a] default = xo := by
    rw [← e1, Array.getD_eq_getD_getElem?]
    unfold K2.skelOf
    rw [stSent_old _ _ _ hlt, hmsg]
    rfl
  rw [eo, hsh] at e2 e3 e4
  refine ⟨e2, e3, ?_, hi, e1, by rw [eo, hsh]⟩
  rw [e4]
  show padPlaces fx.st.codes so = _
  rw [hcs]

/-- **The new copy's shape against the old one's**, behind the program's test on the public
sizes. -/
theorem new_copy (fx : _root_.Tw.K2.Front)
    (hchk : switchTargetCheck (K2.skelOf fx) fx.f.rows fx.T = true) (hcs : fx.st.codes = r.cs)
    (a : ℕ) (hi : a < (switchKept fx.f.rows).size) (h2 : a < fx.T.kept.size) (so : OracleShape)
    (hso : ((K2.skelOf fx).oracles.getD (switchKept fx.f.rows)[a] default).shape = so) :
    fx.T.kept[a].shape.mainRows = so.mainRows ∧
      (r.cs.base.getD fx.T.kept[a].shape.code default).ell =
        (r.cs.base.getD so.code default).ell ∧
      (∀ row place, padRaw r.cs fx.T.kept[a].shape row place ↔ padRaw r.cs so row place) ∧
      eachZ so * so.answers ≤ (r.cs.base.getD so.code default).ell := by
  obtain ⟨c1, c2, c3, c4, c5, -, c7⟩ := check_kept hchk a hi h2
  have ec : (K2.skelOf fx).codes = r.cs := hcs
  rw [hso] at c1 c3 c4 c5 c7
  rw [ec] at c3 c7
  exact ⟨c4, c7, padRaw_same r.cs so _ (c2.trans c1.symm) c4 c5 c7, fit_of_pad r.cs so c1 c3⟩

/-- **The stored sample row at a kept member: its form reads as its coefficients, and a typed seed
fits it**: from the invariant SampleGoodS of the verifier's state. -/
theorem stored_facts (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (hG : K2.SampleGoodS fx.st)
    (hcs : fx.st.codes = r.cs)
    (jN : (plainR r H).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (qN : (plainR r H).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (inj : ∀ a a' : {a // r.kp a}, r.kept.idxOf a.1.1.val = r.kept.idxOf a'.1.1.val → a = a')
    (hmem : ∀ a : {a // r.kp a}, W₀.kept[r.kept.idxOf a.1.1.val]? =
      some (W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩))
    (hrb : ∀ a : {a // r.kp a},
      (W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits = k1 (r.lo.get a.1.1).1)
    (k : {a // (plainHd r H).cl a}) (xo : OnBytes.Oracle)
    (hmsg : fx.st.oracles[(keptK2 r H W₀ k).old]? = some xo)
    (hsh : xo.shape = (r.lo.get k.1.1).1) (hn : xo.sampleRows.size ≠ 0)
    (ha : (r.lo.get k.1.1).1.answers = 1)
    (hc : CaseE (r.lo.get k.1.1).1 ∨ CaseF (r.lo.get k.1.1).1) :
    (∀ i, formAt (formOn (rowK2 r H fx.st W₀ k)) i =
      coefAt (rowK2 r H fx.st W₀ k) (keptK2 r H W₀ k).old .main i) ∧
      ∃ sd, FitsK2 r H fx.st W₀ k sd := by
  obtain ⟨seed, row, y, β, a1, a2, a3, a4⟩ :=
    stored_of_goodS r.cs r.lo r.mem (stageOf r.g 0) r.rad (fun _ => 0) (fun _ => 0) (H.hM 0)
      (H.hZ 0) r.kp (fun a _ => a.2) H.h0 (kqOf r)
      (fun a => W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩) fx.st hG hcs k xo hmsg
      hsh hn ha
  have er : rowK2 r H fx.st W₀ k = { row with target := y } := by
    unfold rowK2
    rw [List.getD_eq_getElem?_getD]
    show ((samplesOf fx.st (W₀.kept.getD (r.kept.idxOf k.1.1.val) ⟨0, 0, 0, 0, [], 0⟩))[0]?).getD
      default = _
    rw [a2]
    rfl
  refine ⟨fun i => ?_, (readP (bitsZ r.cs (r.lo.get k.1.1).1) seed.z, β), ?_⟩
  · rw [er]
    exact stored_reads a1 (H.h0 ⟨k.1.1, k.2.fst⟩ k.2.snd) y i
  · exact seedFits_of_stored r.cs r.lo r.mem (stageOf r.g 0) r.rad (fun _ => 0) (fun _ => 0)
      (H.hM 0) (H.hZ 0) r.kp (fun a _ => a.2) H.h0 (kqOf r) (fun a => r.kept.idxOf a.1.1.val)
      (Letters.plain r H).Sb (Letters.plain r H).sl (Letters.plain r H).Z (Letters.plain r H).A₀
      r.cs r.l W₀ (fun a => W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩) jN qN 0
      (Letters.plain r H).w₀ ⟨0, 0, 0, 0, [], 0⟩ fx.st k inj hmem hrb ha hc seed row y β a1 a2 a3 a4

variable {Xi P : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2) (orc : Strs → ℕ → ℕ → List UInt64)
  (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))

/-- **KeptFacts, as far as the switch's own side pays it.** -/
theorem keptFacts_of (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (hW : K2.frameAt fx = some W₀)
    (hchk : switchTargetCheck (K2.skelOf fx) fx.f.rows fx.T = true) (hcs : fx.st.codes = r.cs)
    (hG : K2.SampleGoodS fx.st)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ (memK (r := r) (H := H)) rowK (plK W₀))
    (inj : ∀ a a' : {a // r.kp a}, r.kept.idxOf a.1.1.val = r.kept.idxOf a'.1.1.val → a = a')
    (hmem : ∀ a : {a // r.kp a}, W₀.kept[r.kept.idxOf a.1.1.val]? =
      some (W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩))
    (hrb : ∀ a : {a // r.kp a},
      (W₀.kept.getD (r.kept.idxOf a.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits = k1 (r.lo.get a.1.1).1)
    (k : {a // (plainHd r H).cl a}) (xo : OnBytes.Oracle)
    (hmsg : fx.st.oracles[(keptK2 r H W₀ k).old]? = some xo)
    (hsh : xo.shape = (r.lo.get k.1.1).1) (hn : xo.sampleRows.size ≠ 0)
    (ha : (r.lo.get k.1.1).1.answers = 1)
    (hc : CaseE (r.lo.get k.1.1).1 ∨ CaseF (r.lo.get k.1.1).1)
    (hT : ∀ ho : 1 + r.kept.idxOf k.1.1.val < r.l.length,
      ∃ h2 : r.kept.idxOf k.1.1.val < fx.T.kept.size,
        (r.l.get ⟨_, ho⟩).1 = fx.T.kept[r.kept.idxOf k.1.1.val].shape)
    (hst : a.2.st.oracles = fx.st.oracles)
    (hseat : KeptSeat G p t fx (orc y) y (keptK2 r H W₀ k).old (r.lo.get k.1.1).1 (seat k.1.1)
      (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a))
    (hlist : seat k.1.1 ∈ seats)
    (hnum : numAt seats ⟨⟨r.lo, seat⟩, k.1.1⟩ = (keptK2 r H W₀ k).old)
    (hone : ∀ ho : 1 + r.kept.idxOf k.1.1.val < r.l.length,
      arr (seatN ⟨_, ho⟩).1 (seatN ⟨_, ho⟩).2 = arr (seat k.1.1).1 (seat k.1.1).2)
    (hshown : ShownAt G r.cs r.lo seat y k.1.1) :
    KeptFacts G seat seatN p orc arr seats a t fx W₀ y k (keptK2 r H W₀ k) xo := by
  have hat : W₀.kept[r.kept.idxOf k.1.1.val]? = some (keptK2 r H W₀ k) :=
    hmem ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩
  obtain ⟨s1, s2, s3, hi, -, s5⟩ := entry_shape fx W₀ hW hcs _ _ hat xo hmsg _ hsh
  have hpos : 0 < (r.lo.get k.1.1).1.mainRows := Nat.pos_of_ne_zero k.2.fst
  obtain ⟨ho, -, -, -⟩ := Ft.keptMsg (slotOf k ⟨0, hpos⟩)
  obtain ⟨h2, eT⟩ := hT ho
  obtain ⟨n1, n2, n3, n4⟩ := new_copy (r := r) fx hchk hcs _ hi h2 _ s5
  obtain ⟨f1, f2⟩ := stored_facts fx W₀ hG hcs
    (Johnson.Top.H.iJ (plainR r H).s W₀ memK rowK (plK W₀) r.cs r.l Ft.nameJ)
    (Johnson.Top.H.iQ (plainR r H).s W₀ memK rowK r.cs r.l Ft.nameQ) inj hmem hrb k xo hmsg hsh hn
    ha hc
  rw [ha, Nat.mul_one] at n4
  exact
    { at' := hat, rows := s1, bits := s2, pad := s3, seatIs := hseat, one := ha, fit := n4
      new := ⟨ho, by rw [eT]; exact n1, by rw [eT]; exact n2, by rw [eT]; exact n3, hone ho⟩
      st := hst, listed := hlist, num := hnum, msg := hmsg, stored := hn, reads := f1, fits := f2
      shown := hshown }

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptFacts_of

#print axioms VerifiableInference.Desc.First.K2Caller.entry_shape
#print axioms VerifiableInference.Desc.First.K2Caller.new_copy
#print axioms VerifiableInference.Desc.First.K2Caller.stored_facts
