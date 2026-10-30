-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieDone.lean: THE TABLE'S
THREE SENTENCES BEHIND THE KIND'S OWN BLOCK GIVE THE TYPED LOOKUP'S OUT-RELATION:
FormsObjects, WorthPlanes and WorthKeys (Johnson/Desc/Key/KeyK3Items.lean), at "two elements are the
same where they read alike", give A.Done of the entries at the out read off the ledger in which the
kind's own closing ends (outOf: Johnson/Desc/First/Look/KeyLaw/Statement.lean). One way.

Main names:
  key_cut: the library's key reads the matrix inside its size.
  mem_home: a slot below the homes' size has its home in the table's list.
  rowA_holds, rowP_holds: one typed row from one sentence's clause (the side clause "every slot
    below the homes' size" is spent here).
  rows_of_sentences: all rows of rowsF. keys_of_sentence: all parts' claims.
  done_of_sentences: THE JOIN.

Object: the table's and K3's terms; the typed lookup A under A.toPub = pubOf (Wf.lookupOf id m l).
User: claim_behind₀ (TieClaimBehind.lean).
Letters: A, sl, st, μ: the typed lookup, the placing of mask entries, a state, the entries · w: the
words to which the entries are tied (Tied) · mk, bit, mat: the mask entries, the bits and the matrix
in machine elements. Premises on them: mk, at the table's homes, and bit, at the real indices, read
as w says; the typed keys are the library's at the matrix read and cut.

Limits. One way. That closedAt returns is a clause of the sentences, not shown. Where there are not
three claims on the planes, or no last object, rowsF is empty and the rows' half says nothing: the
sentence's clause "three claims" is not spent. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieReadP
import Johnson.RunOne.Law.TieReadK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieDone
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open OnBytes.Params (WfRun WfPart WfLookup WfPublic)
open Lk6 (Dat pubOf)
open Lk6.Mid (rdCl rdRow)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (affAt planeSum closedAt Zero FormsObjects WorthPlanes WorthKeys
  keyVec sumE)
open Johnson.RunOne.Law.TieRead
open Johnson.RunOne.Law.TieReadP
open Johnson.RunOne.Law.TieReadK
open Johnson.RunOne.Law.TieKeys

/-- The library's key reads the matrix inside its size. -/
theorem key_cut (m : Wf.Matrix) (L : Leaves.LkF) (M : ℕ → ℕ → GE) (runs : List WfRun)
    (hR : Leaves.RowsIn L m.rows runs) (n : ℕ) :
    Leaves.key L (cutM m M) m.kCol runs n = Leaves.key L M m.kCol runs n := by
  unfold Leaves.key
  have hcol : n % 2 ^ m.kCol < 2 ^ m.kCol := Nat.mod_lt _ (Nat.pow_pos (by omega))
  generalize n / 2 ^ m.kCol = place
  have go : ∀ rs : List WfRun, (∀ r ∈ rs, r ∈ runs) →
      Leaves.keyAt L (cutM m M) rs place (n % 2 ^ m.kCol) =
        Leaves.keyAt L M rs place (n % 2 ^ m.kCol) := by
    intro rs
    induction rs with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro hm
      unfold Leaves.keyAt
      by_cases h : r.firstPlace ≤ place ∧ place < r.firstPlace + r.places
      · rw [if_pos h, if_pos h]
        exact runKey_cut m L M runs hR r (hm r List.mem_cons_self) _ _ h hcol
      · rw [if_neg h, if_neg h]
        exact ih fun q hq => hm q (List.mem_cons_of_mem _ hq)
  exact go runs fun _ h => h

/-- A slot below the homes' size has its home in the table's list. -/
theorem mem_home (homeA : Array Slot) (n : ℕ) (h : n < homeA.size) :
    homeA.getD n default ∈ homeA.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  exact Array.getElem_mem_toList h

theorem mfOf_home (G : Fork) (homeA : Array Slot) (a : Aff)
    (h : ∀ t ∈ a.slots, t.1 < homeA.size) :
    ∀ p ∈ mfOf G (fun n => homeA.getD n default) a, p.1 ∈ homeA.toList := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
  exact mem_home homeA t.1 (h t (Array.mem_toList_iff.1 ht))

section
variable {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE} {x : WfPublic}
  {codes : Codes} {i : ℕ} {homeA : Array Slot} (hr : A.pl ≤ 2 ^ A.mu)
  (hT : Tied A sl μ w x codes i homeA.toList) (l : WfLookup) (hi : x.lookups[i]? = some l)
  (hpl : Wf.planesOf l = A.pl) (G : Fork) (mk : Slot → E)
  (hmk : ∀ s ∈ homeA.toList, w s.oracle .mask s.index = readE (mk s))
include hr hT hi hpl hmk

/-- One typed row from "the form is worth 0". -/
theorem rowA_holds (a : Aff) (hs : ∀ t ∈ a.slots, t.1 < homeA.size)
    (h : readE (affAt G homeA mk a) = readE zeroE) :
    (rdRow A sl (rowA G (fun n => homeA.getD n default) a)).Holds μ := by
  have hin : ∀ p ∈ (rowA G (fun n => homeA.getD n default) a).masks, p.1 ∈ homeA.toList := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact mfOf_home G homeA a hs q hq
  refine (typed_iff hr hT l hi hpl _ hin).2 ?_
  rw [← (zero_iff_rowA G homeA mk A.mu A.d
    (fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j) a).1 h]
  exact valueF_congr A.mu A.d _ (fun p hp => hmk p.1 (hin p hp)) fun _ _ _ _ => rfl

/-- One typed row from the sentence on a claim that reads the planes. -/
theorem rowP_holds (f : Face) (hmu : f.mu = A.mu) (hd : f.d = A.d) (bit : ℕ → E)
    (hbit : ∀ n < 2 ^ (f.mu + f.d), readE (bit n) =
      Planes.bitsOf x codes i (w x.messageId .main) (n / 2 ^ f.mu) (n % 2 ^ f.mu))
    (turned : Bool) (c : PlaneClaim) (hs : ∀ t ∈ c.lead.slots, t.1 < homeA.size)
    (h : readE (addE (affAt G homeA mk c.lead) (mulE c.scalar (planeSum f c.pairs bit))) =
      readE zeroE) :
    (rdRow A sl (rowP G (fun n => homeA.getD n default) turned c)).Holds μ := by
  have hin : ∀ p ∈ (rowP G (fun n => homeA.getD n default) turned c).masks,
      p.1 ∈ homeA.toList := by
    intro p hp
    cases turned with
    | true =>
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact mfOf_home G homeA c.lead hs q hq
    | false => exact mfOf_home G homeA c.lead hs p hp
  refine (typed_iff hr hT l hi hpl _ hin).2 ?_
  have e := (plane_iff_rowP G homeA mk f c bit turned).1 h
  rw [hmu, hd] at e
  rw [← e]
  refine valueF_congr A.mu A.d _ (fun p hp => hmk p.1 (hin p hp)) fun j hj t ht => ?_
  rw [← hmu] at hj ⊢
  rw [← hd] at ht
  have hn : j + 2 ^ f.mu * t < 2 ^ (f.mu + f.d) := by
    rw [Nat.pow_add]
    have h1 : 2 ^ f.mu * (t + 1) ≤ 2 ^ f.mu * 2 ^ f.d := Nat.mul_le_mul_left _ ht
    rw [Nat.mul_succ] at h1
    omega
  rw [hbit _ hn, Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hj,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

end

section
variable {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE} {x : WfPublic}
  {codes : Codes} {i : ℕ} {homeA : Array Slot} (hr : A.pl ≤ 2 ^ A.mu)
  (hT : Tied A sl μ w x codes i homeA.toList) (l : WfLookup) (hi : x.lookups[i]? = some l)
  (hpl : Wf.planesOf l = A.pl) (G : Fork) (mk : Slot → E)
  (hmk : ∀ s ∈ homeA.toList, w s.oracle .mask s.index = readE (mk s))
include hr hT hi hpl hmk

/-- **All rows of the typed out, from the sentences on the forms and on the planes.** -/
theorem rows_of_sentences (f : Face) (hmu : f.mu = A.mu) (hd : f.d = A.d) (bit : ℕ → E)
    (hbit : ∀ n < 2 ^ (f.mu + f.d), readE (bit n) =
      Planes.bitsOf x codes i (w x.messageId .main) (n / 2 ^ f.mu) (n % 2 ^ f.mu))
    (objects : List Aff) (cl : List PlaneClaim)
    (hF : ∀ a ∈ objects, Zero (fun a b => readE a = readE b) G homeA mk a)
    (hC : ∀ c ∈ cl, c.lead.ents.isEmpty = true ∧ (∀ t ∈ c.lead.slots, t.1 < homeA.size) ∧
      readE (addE (affAt G homeA mk c.lead) (mulE c.scalar (planeSum f c.pairs bit))) =
        readE zeroE) :
    Cb.LdLkp.RowsHold ((rowsF G (fun n => homeA.getD n default) objects cl).map (rdRow A sl)) μ :=
        by
  have ra := fun a (ha : a ∈ objects) =>
    rowA_holds hr hT l hi hpl G mk hmk a (hF a ha).2.1 (hF a ha).2.2
  have rp := fun t c (hc : c ∈ cl) =>
    rowP_holds hr hT l hi hpl G mk hmk f hmu hd bit hbit t c (hC c hc).2.1 (hC c hc).2.2
  intro r hrm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hrm
  unfold rowsF at hq
  split at hq
  · rename_i leaves value counts bits hg
    rcases List.mem_append.1 hq with h1 | h1
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h1
      exact ra a (List.mem_of_mem_dropLast ha)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl
      · exact rp true leaves (by simp)
      · exact ra bits (List.mem_of_getLast? hg)
      · exact rp false value (by simp)
      · exact rp true counts (by simp)
  · cases hq

/-- **All parts' claims of the typed out, from the sentence on the keys.** -/
theorem keys_of_sentence (st : A.St) (id : ℕ) (m : Wf.Matrix) (mat : ℕ → ℕ → F)
    (hP : A.toPub = pubOf (Wf.lookupOf id m l)) (hlo : Wf.lookupOk Wf.fBits l = true)
    (hfm : Wf.fitsMatrix m l = true) (hK : KeysAre A st μ id m l (cutM m (matR mat)))
    (g : HeardG) (k1 : g.keys.length = l.parts.length)
    (k2 : ∀ q < l.parts.length, (g.keys.getD q (#[], {})).1.size = A.v q)
    (hW : ∀ y ∈ g.keys.zipIdx, y.1.2.ents.isEmpty = true ∧
      (∀ t ∈ y.1.2.slots, t.1 < homeA.size) ∧
      readE (affAt G homeA mk y.1.2) = readE (sumE (2 ^ A.v y.2) fun k =>
        mulE ((Tensor.eq y.1.1.toList.reverse).entry k) (subE g.alpha (keyVec m l mat y.2 k))))
    (j : Fin A.m) :
    (rdCl A sl (readE g.alpha) (A.v j) (keyF G (fun n => homeA.getD n default)
      (g.keys.getD j (#[], {})))).Holds (A.v j) (A.key st μ j) μ := by
  have hm' : A.m = l.parts.length := by
    show A.toPub.parts.length = _
    rw [hP]
    exact List.length_map _
  have hj : j.val < l.parts.length := by
    rw [← hm']
    exact j.isLt
  have hp : l.parts[j.val]? = some l.parts[j.val] := List.getElem?_eq_getElem hj
  have hjk : j.val < g.keys.zipIdx.length := by
    rw [List.length_zipIdx, k1]
    exact hj
  have hz : g.keys.zipIdx[j.val] = (g.keys.getD j.val (#[], {}), j.val) := by
    rw [List.getElem_zipIdx, Nat.zero_add, List.getD_eq_getElem]
  have hmem : (g.keys.getD j.val (#[], {}), j.val) ∈ g.keys.zipIdx := hz ▸ List.getElem_mem hjk
  obtain ⟨-, s2, s3⟩ := hW _ hmem
  have hpk : l.paddingKey.toNat < 2 ^ l.d := by
    have h := hlo
    simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2
  refine (key_iff_rdCl G homeA mk g.alpha (A.v j) _ (k2 j.val hj) (keyVec m l mat j.val) _
    (fun n _ => ?_) fun q hq => ?_).1 s3
  · rw [hK j.val _ hp, key_cut m _ _ _ (Leaves.rowsIn_of _ (List.length_map _) hfm
      (List.getElem_mem hj)), read_keyVec m l mat j.val _ hp n, Leaves.read_padOf id m l zeroE hpk]
  · rw [hT.mask q.1 (mfOf_home G homeA _ s2 q hq), hmk q.1 (mfOf_home G homeA _ s2 q hq)]

end

/-- **THE THREE SENTENCES GIVE THE TYPED OUT-RELATION**, at the ledger in which the kind's own
closing ends. -/
theorem done_of_sentences {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE}
    {x : WfPublic} {codes : Codes} {i : ℕ} {homeA : Array Slot} (hadm : A.toPub.Adm Cb.Gl.p)
    (hT : Tied A sl μ w x codes i homeA.toList) (l : WfLookup) (hi : x.lookups[i]? = some l)
    (mk : Slot → E) (hmk : ∀ s ∈ homeA.toList, w s.oracle .mask s.index = readE (mk s)) (st : A.St)
        (id : ℕ)
    (m : Wf.Matrix) (mat : ℕ → ℕ → F) (hP : A.toPub = pubOf (Wf.lookupOf id m l))
    (hlo : Wf.lookupOk Wf.fBits l = true) (hfm : Wf.fitsMatrix m l = true)
    (hK : KeysAre A st μ id m l (cutM m (matR mat))) (bit : ℕ → E)
    (hbit : ∀ n < 2 ^ ((faceOfLkp (Wf.lookupOf id m l)).mu + (faceOfLkp (Wf.lookupOf id m l)).d),
      readE (bit n) = Planes.bitsOf x codes i (w x.messageId .main)
        (n / 2 ^ (faceOfLkp (Wf.lookupOf id m l)).mu)
        (n % 2 ^ (faceOfLkp (Wf.lookupOf id m l)).mu))
    (g : HeardG) (G : Fork)
    (k2 : ∀ q < l.parts.length, (g.keys.getD q (#[], {})).1.size = A.v q)
    (h1 : FormsObjects (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk)
    (h2 : WorthPlanes (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk
      bit)
    (h3 : WorthKeys (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk
      (keyVec m l mat)) :
    ∃ cl G', closedAt (faceOfLkp (Wf.lookupOf id m l)) g G = some (cl, G') ∧
      A.Done μ (outOf A sl st G' (fun n => homeA.getD n default) g cl) := by
  obtain ⟨cl, G', e1, f1⟩ := h1
  obtain ⟨cl2, G2, e2, -, f2⟩ := h2
  obtain ⟨kl, cl3, G3, e3, f3⟩ := h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (e1.symm.trans e2))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (e1.symm.trans e3))
  have hv : ∀ q, A.v q = (faceOfLkp (Wf.lookupOf id m l)).parts.getD q 0 := fun q => by
    show A.toPub.parts.getD q 0 = _
    rw [hP]
    rfl
  refine ⟨cl, G', e1, ?_⟩
  unfold Lk6.Dat.Done
  exact ⟨keys_of_sentence hadm.room hT l hi (congrArg Lk6.Pub.pl hP).symm G' mk hmk st id m mat hP
      hlo hfm hK g (kl.trans (List.length_map _)) k2 fun y hy => by
        rw [hv]
        exact f3 y hy,
    rows_of_sentences hadm.room hT l hi (congrArg Lk6.Pub.pl hP).symm G' mk hmk _
      (congrArg Lk6.Pub.mu hP).symm (congrArg Lk6.Pub.d hP).symm bit hbit _ cl f1 f2⟩

end Johnson.RunOne.Law.TieDone

#print axioms Johnson.RunOne.Law.TieDone.key_cut
#print axioms Johnson.RunOne.Law.TieDone.rowA_holds
#print axioms Johnson.RunOne.Law.TieDone.rowP_holds
#print axioms Johnson.RunOne.Law.TieDone.rows_of_sentences
#print axioms Johnson.RunOne.Law.TieDone.keys_of_sentence
#print axioms Johnson.RunOne.Law.TieDone.done_of_sentences
