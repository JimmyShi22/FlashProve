-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SaysAtFirstEnd.lean: hFirst OF samples_at_lastThread (Honest/K12/AtFile/LotWJointSamplesAtLastThread.lean), FROM THE PINS' MEANING AT THE FIRST CHAIN's END: a pin's answer at the library's reader of samples is the first sample row's claim (ans_iff_says, K1/Law/SaysMeets.lean), of the words that the witness gives through that chain's last statement and book.

  words_at_entry     wordsOn at an entry's own table (partZ) and index (locZ) is the entry
  sampleSays_of_smp  one message: one sample row; its sample at the reader's seed has its answers in the table T
  sampleSays_of_ans  the same from AnsAt at a member of the reader's list
  sampleItem_of_ans  hFirst's end at every f, G, from one answering member for each message of the group

What is not here. The premise hM is on the first chain's end as parts.ends names it: LastThreadParts.ends and .meaning are free fields: that the state they give is the first chain's end and that its pins mean the first thread's is ProofFile's tie, owed.

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import Johnson.Desc.ProofFile.Honest.K1.Law.SaysMeets
import Johnson.Desc.ProofFile.Honest.Thread.Ans
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.WordsAt
import Johnson.Desc.Third.Border
import Johnson.Desc.Means.ItemsAt
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Means
open OnBytes.Slice (rdE GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem Sending seatOf seatBy noFirst msgsOf numAt smpNamed smpNamed_at wordsBy wordsFirst tabAt)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K1 (smpAt)
open Johnson.Pack
open VerifiableInference.Desc.First.Close (NamesOne)

/-- wordsOn at an entry's own table and index is the entry. -/
theorem words_at_entry {K : Type} [CommRing K] (St : Statement) {o : ℕ} {x : Oracle} (hx : St.oracles[o]? = some x)
    (T : ℕ → Bool → ℕ → ℕ → K) (cs : Codes) (j : (portCode cs x.shape).J) :
    wordsOn St T o (partZ cs x.shape j) (locZ cs x.shape j) =
      match j with
      | .inl q => T o false q.1.val q.2.val
      | .inr q => T o true q.1.val q.2.val := by
  rcases j with y | y
  · have hr : y.1.val < 2 ^ k1 x.shape := lt_of_lt_of_le y.1.isLt (OnBytes.Slice.le_two_pow_ceilLog2 _)
    have h1 : (y.1.val + 2 ^ k1 x.shape * y.2.val) % 2 ^ k1 x.shape = y.1.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have h2 : (y.1.val + 2 ^ k1 x.shape * y.2.val) / 2 ^ k1 x.shape = y.2.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
    have hb : St.rowBits o .main = k1 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    have hR : realRows St o .main = x.shape.mainRows := by
      unfold realRows
      rw [hx]
      rfl
    show wordsOn St T o .main (y.1.val + 2 ^ k1 x.shape * y.2.val) = _
    unfold wordsOn
    rw [hb, hR, h1, h2, if_pos y.1.isLt]
    rfl
  · have hr : y.1.val < 2 ^ k2 x.shape := lt_of_lt_of_le y.1.isLt (OnBytes.Slice.le_two_pow_ceilLog2 _)
    have h1 : (y.1.val + 2 ^ k2 x.shape * y.2.val) % 2 ^ k2 x.shape = y.1.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have h2 : (y.1.val + 2 ^ k2 x.shape * y.2.val) / 2 ^ k2 x.shape = y.2.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
    have hb : St.rowBits o .mask = k2 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    have hR : realRows St o .mask = x.shape.maskRows := by
      unfold realRows
      rw [hx]
      rfl
    show wordsOn St T o .mask (y.1.val + 2 ^ k2 x.shape * y.2.val) = _
    unfold wordsOn
    rw [hb, hR, h1, h2, if_pos y.1.isLt]
    rfl

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **One message, its one sample row, from its sample's answers.** -/
theorem sampleSays_of_smp (St : Statement) {o : ℕ} {x : Oracle} (hx : St.oracles[o]? = some x)
    {r : Row} (hr : x.sampleRows.toList = [r]) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain St.codes x.shape).ell = (pMain St.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask St.codes x.shape).ell = (pMask St.codes x.shape).ell)
    (seatAt : ℕ → Option (ℕ × ℕ)) (w : Wit Cells Tok MsgT) {q : ℕ × ℕ} (hs : seatAt o = some q)
    (p : OracleShape × ℕ) (hp : p.1 = x.shape) (z : (portOmZ St.codes p.1 p.2).Smp)
    (hz : smpAt St.codes p.1 p.2 St o = some z) (T : MsgT)
    (hT : T = w.tab St.codes x.shape (arr q.1 q.2) q.1 q.2)
    (hv : (portOmZ St.codes p.1 p.2).Z.val z.1
      (fun j => match (j : (Fin p.1.mainRows × Fin (pMain St.codes p.1).ell) ⊕
          (Fin p.1.maskRows × Fin (pMask St.codes p.1).ell)) with
        | .inl y => T false y.1.val y.2.val
        | .inr y => T true y.1.val y.2.val) = z.2) :
    SampleSays rdE St o (wordsBy arr seatAt St w) := by
  obtain ⟨sh, e⟩ := p
  obtain rfl : sh = x.shape := hp
  intro x' hx'
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  have hr0 : x.sampleRows[0]? = some r := by
    rw [← Array.getElem?_toList, hr]
    rfl
  have hP := padded_wordsOn St (tabAt St.codes arr seatAt St w)
  have key := (ans_iff_says St o x hx r hr0 hN hlM hlZ
    (wordsBy arr seatAt St w) hP e z hz).1 (by
      rw [← hv]
      congr 1
      funext j
      show wordsOn St (tabAt St.codes arr seatAt St w) o _ _ = _
      rw [words_at_entry St hx _ St.codes j]
      have eT : tabAt St.codes arr seatAt St w o = T := by
        unfold tabAt
        rw [hs, hx, hT]
      rw [eT]
      rcases j with y | y <;> rfl)
  intro r' hr'
  rw [hr] at hr'
  obtain rfl := List.mem_singleton.1 hr'
  exact key

/-- **The same from a pin's answer at a member of the reader's list.** -/
theorem sampleSays_of_ans {Pb : Type} (seats : List (ℕ × ℕ)) {p : Pb} {s : S} {o : ℕ} {x : Oracle}
    (hx : s.st.oracles[o]? = some x) {r : Row} (hr : x.sampleRows.toList = [r]) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain s.st.codes x.shape).ell = (pMain s.st.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask s.st.codes x.shape).ell = (pMask s.st.codes x.shape).ell)
    (seatAt : ℕ → Option (ℕ × ℕ)) (w : Wit Cells Tok MsgT) (μ : Mem)
    (hs : seatAt o = some (seatOf μ)) (hq : μ.1.seat μ.2 ∈ seats) (hno : numAt seats μ = o)
    (hsh : (μ.1.l.get μ.2).1 = x.shape)
    (hA : AnsAt s.st.codes arr μ.1.l μ.1.seat (fun a => smpNamed s.st.codes seats a μ.1) μ.2 (p, s) w) :
    SampleSays rdE s.st o (wordsBy arr seatAt s.st w) := by
  obtain ⟨z, hz, hv⟩ := hA
  have hz' : smpAt s.st.codes (μ.1.l.get μ.2).1 (μ.1.l.get μ.2).2 s.st o = some z := by
    have e := smpNamed_at s.st.codes seats (p, s) μ.1 μ.2 hq
    rw [hno] at e
    exact e.symm.trans hz
  refine sampleSays_of_smp arr s.st hx hr hN hlM hlZ seatAt w hs (μ.1.l.get μ.2) hsh z hz'
    (w.tab s.st.codes (μ.1.l.get μ.2).1 (arr (seatOf μ).1 (seatOf μ).2) (seatOf μ).1 (seatOf μ).2)
    (by rw [hsh]) ?_
  rw [← hv]
  congr 1
  funext j
  rcases j with y | y <;> rfl

/-- **hFirst's end, from one answering member at each message of the group.** -/
theorem sampleItem_of_ans {Pb : Type} (seats : List (ℕ × ℕ)) {p : Pb} {s : S}
    {f : VerifiableInference.Desc.Third.FirstEnd₃} (hf : firstOfS s = some f)
    {os : List ℕ} (w : Wit Cells Tok MsgT)
    (hM : ∀ o ∈ os, ∃ (x : Oracle) (r : Row) (μ : Mem), s.st.oracles[o]? = some x ∧
      x.sampleRows.toList = [r] ∧ NamesOne r o ∧
      (0 < x.shape.mainRows →
        2 ^ ceilLog2 (pMain s.st.codes x.shape).ell = (pMain s.st.codes x.shape).ell) ∧
      (0 < x.shape.maskRows →
        2 ^ ceilLog2 (pMask s.st.codes x.shape).ell = (pMask s.st.codes x.shape).ell) ∧
      seatBy noFirst s.book o = some (seatOf μ) ∧ μ.1.seat μ.2 ∈ seats ∧ numAt seats μ = o ∧
      (μ.1.l.get μ.2).1 = x.shape ∧
      AnsAt s.st.codes arr μ.1.l μ.1.seat (fun a => smpNamed s.st.codes seats a μ.1) μ.2 (p, s) w) :
    sampleItem rdE f.st os (wordsFirst arr f.st f.book w) := by
  obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.1 hf
  intro o ho
  obtain ⟨x, r, μ, hx, hr, hN, hlM, hlZ, hs, hq, hno, hsh, hA⟩ := hM o ho
  exact sampleSays_of_ans arr seats hx hr hN hlM hlZ (seatBy noFirst s.book) w μ hs hq hno hsh hA

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.words_at_entry
#print axioms ProofFile.Honest.K1.sampleSays_of_smp
#print axioms ProofFile.Honest.K1.sampleSays_of_ans
#print axioms ProofFile.Honest.K1.sampleItem_of_ans
