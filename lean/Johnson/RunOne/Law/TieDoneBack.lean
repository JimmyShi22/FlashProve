-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieDoneBack.lean: THE TYPED
LOOKUP'S OUT-RELATION GIVES THE TABLE'S THREE SENTENCES BEHIND THE KIND'S OWN BLOCK: the converse of
done_of_sentences (TieDone.lean): A.Done of the entries, at the out read off the ledger in which the
kind's own closing ends, gives FormsObjects, WorthPlanes and WorthKeys
(Johnson/Desc/Key/KeyK3Items.lean) at "read alike": WHERE THE SENTENCES' SIDE CLAUSES HOLD (Side,
TieSide.lean), there are three claims on the planes, an object, and a claim on keys a part.

Main names:
  rowA_zero, rowP_sentence: one clause of a sentence from one typed row.
  sentences_of_done: THE JOIN.

Object: the table's and K3's terms; the typed lookup A under A.toPub = pubOf (Wf.lookupOf id m l).
User: claim_front_layer₀, claim_front_layer₁ (TieFrontLayer.lean).
Letters and premises on them: those of done_of_sentences.

Limits. One way. The side clauses and closedAt's yes are premises. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieDone
import Johnson.RunOne.Law.TieSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieDoneBack
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
open Johnson.RunOne.Law.TieDone
open Johnson.RunOne.Law.TieSide

section
variable {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE} {x : WfPublic}
  {codes : Codes} {i : ℕ} {homeA : Array Slot} (hr : A.pl ≤ 2 ^ A.mu)
  (hT : Tied A sl μ w x codes i homeA.toList) (l : WfLookup) (hi : x.lookups[i]? = some l)
  (hpl : Wf.planesOf l = A.pl) (G : Fork) (mk : Slot → E)
  (hmk : ∀ s ∈ homeA.toList, w s.oracle .mask s.index = readE (mk s))
include hr hT hi hpl hmk

/-- "The form is worth 0" from its typed row. -/
theorem rowA_zero (a : Aff) (hs : ∀ t ∈ a.slots, t.1 < homeA.size)
    (h : (rdRow A sl (rowA G (fun n => homeA.getD n default) a)).Holds μ) :
    readE (affAt G homeA mk a) = readE zeroE := by
  have hin : ∀ p ∈ (rowA G (fun n => homeA.getD n default) a).masks, p.1 ∈ homeA.toList := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact mfOf_home G homeA a hs q hq
  refine (zero_iff_rowA G homeA mk A.mu A.d
    (fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j) a).2 ?_
  rw [← (typed_iff hr hT l hi hpl _ hin).1 h]
  exact (valueF_congr A.mu A.d _ (fun p hp => hmk p.1 (hin p hp)) fun _ _ _ _ => rfl).symm

/-- The sentence on a claim that reads the planes from its typed row. -/
theorem rowP_sentence (f : Face) (hmu : f.mu = A.mu) (hd : f.d = A.d) (bit : ℕ → E)
    (hbit : ∀ n < 2 ^ (f.mu + f.d), readE (bit n) =
      Planes.bitsOf x codes i (w x.messageId .main) (n / 2 ^ f.mu) (n % 2 ^ f.mu))
    (turned : Bool) (c : PlaneClaim) (hs : ∀ t ∈ c.lead.slots, t.1 < homeA.size)
    (h : (rdRow A sl (rowP G (fun n => homeA.getD n default) turned c)).Holds μ) :
    readE (addE (affAt G homeA mk c.lead) (mulE c.scalar (planeSum f c.pairs bit))) =
      readE zeroE := by
  have hin : ∀ p ∈ (rowP G (fun n => homeA.getD n default) turned c).masks,
      p.1 ∈ homeA.toList := by
    intro p hp
    cases turned with
    | true =>
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact mfOf_home G homeA c.lead hs q hq
    | false => exact mfOf_home G homeA c.lead hs p hp
  refine (plane_iff_rowP G homeA mk f c bit turned).2 ?_
  rw [hmu, hd, ← (typed_iff hr hT l hi hpl _ hin).1 h]
  refine (valueF_congr A.mu A.d _ (fun p hp => hmk p.1 (hin p hp)) fun j hj t ht => ?_).symm
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

/-- **THE TYPED OUT-RELATION GIVES THE THREE SENTENCES**, where their side clauses hold. -/
theorem sentences_of_done {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE}
    {x : WfPublic} {codes : Codes} {i : ℕ} {homeA : Array Slot} (hadm : A.toPub.Adm Cb.Gl.p)
    (hT : Tied A sl μ w x codes i homeA.toList) (l : WfLookup) (hi : x.lookups[i]? = some l)
    (mk : Slot → E) (hmk : ∀ s ∈ homeA.toList, w s.oracle .mask s.index = readE (mk s))
    (st : A.St) (id : ℕ) (m : Wf.Matrix) (mat : ℕ → ℕ → F)
    (hP : A.toPub = pubOf (Wf.lookupOf id m l)) (hlo : Wf.lookupOk Wf.fBits l = true)
    (hfm : Wf.fitsMatrix m l = true) (hK : KeysAre A st μ id m l (cutM m (matR mat)))
    (bit : ℕ → E)
    (hbit : ∀ n < 2 ^ ((faceOfLkp (Wf.lookupOf id m l)).mu + (faceOfLkp (Wf.lookupOf id m l)).d),
      readE (bit n) = Planes.bitsOf x codes i (w x.messageId .main)
        (n / 2 ^ (faceOfLkp (Wf.lookupOf id m l)).mu)
        (n % 2 ^ (faceOfLkp (Wf.lookupOf id m l)).mu))
    (g : HeardG) (G G' : Fork) (cl : List PlaneClaim)
    (hc : closedAt (faceOfLkp (Wf.lookupOf id m l)) g G = some (cl, G'))
    (k1 : g.keys.length = l.parts.length)
    (k2 : ∀ q < l.parts.length, (g.keys.getD q (#[], {})).1.size = A.v q)
    (hne : g.rows.toList ≠ []) (h3 : cl.length = 3)
    (sO : ∀ a ∈ g.rows.toList, Side homeA a) (sP : ∀ c ∈ cl, Side homeA c.lead)
    (sK : ∀ y ∈ g.keys.zipIdx, Side homeA y.1.2)
    (hD : A.Done μ (outOf A sl st G' (fun n => homeA.getD n default) g cl)) :
    FormsObjects (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk ∧
    WorthPlanes (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk bit ∧
    WorthKeys (fun a b => readE a = readE b) (faceOfLkp (Wf.lookupOf id m l)) g G homeA mk
      (keyVec m l mat) := by
  unfold Lk6.Dat.Done at hD
  obtain ⟨hKeys, hRows⟩ : (∀ j : Fin A.m, (rdCl A sl (readE g.alpha) (A.v j)
      (keyF G' (fun n => homeA.getD n default) (g.keys.getD j (#[], {})))).Holds (A.v j)
        (A.key st μ j) μ) ∧
    Cb.LdLkp.RowsHold ((rowsF G' (fun n => homeA.getD n default) g.rows.toList cl).map
      (rdRow A sl)) μ := hD
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ a b c, cl = [a, b, c] := by
    match cl, h3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hpl := (congrArg Lk6.Pub.pl hP).symm
  have hmu := (congrArg Lk6.Pub.mu hP).symm
  have hd := (congrArg Lk6.Pub.d hP).symm
  have hg : g.rows.toList.getLast? = some (g.rows.toList.getLast hne) :=
    List.getLast?_eq_getLast hne
  have hF : rowsF G' (fun n => homeA.getD n default) g.rows.toList [c0, c1, c2] =
      g.rows.toList.dropLast.map (rowA G' fun n => homeA.getD n default) ++
        [rowP G' (fun n => homeA.getD n default) true c0,
          rowA G' (fun n => homeA.getD n default) (g.rows.toList.getLast hne),
          rowP G' (fun n => homeA.getD n default) false c1,
          rowP G' (fun n => homeA.getD n default) true c2] := by
    unfold rowsF
    rw [hg]
  rw [hF] at hRows
  have row : ∀ r, r ∈ g.rows.toList.dropLast.map (rowA G' fun n => homeA.getD n default) ++
        [rowP G' (fun n => homeA.getD n default) true c0,
          rowA G' (fun n => homeA.getD n default) (g.rows.toList.getLast hne),
          rowP G' (fun n => homeA.getD n default) false c1,
          rowP G' (fun n => homeA.getD n default) true c2] → (rdRow A sl r).Holds μ :=
    fun r hr => hRows _ (List.mem_map.2 ⟨r, hr, rfl⟩)
  have hv : ∀ q, A.v q = (faceOfLkp (Wf.lookupOf id m l)).parts.getD q 0 := fun q => by
    show A.toPub.parts.getD q 0 = _
    rw [hP]
    rfl
  refine ⟨⟨_, G', hc, fun a ha => ⟨(sO a ha).1, (sO a ha).2, ?_⟩⟩,
    ⟨_, G', hc, rfl, fun c hcm => ⟨(sP c hcm).1, (sP c hcm).2, ?_⟩⟩,
    k1.trans (List.length_map _).symm, _, G', hc, fun y hy => ⟨(sK y hy).1, (sK y hy).2, ?_⟩⟩
  · refine rowA_zero hadm.room hT l hi hpl G' mk hmk a (sO a ha).2 (row _ ?_)
    rw [← List.dropLast_append_getLast hne] at ha
    rcases List.mem_append.1 ha with h5 | h5
    · exact List.mem_append_left _ (List.mem_map.2 ⟨a, h5, rfl⟩)
    · obtain rfl := List.mem_singleton.1 h5
      exact List.mem_append_right _ (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl
    · exact rowP_sentence hadm.room hT l hi hpl G' mk hmk _ hmu hd bit hbit true _
        (sP _ (by simp)).2 (row _ (List.mem_append_right _ (by simp)))
    · exact rowP_sentence hadm.room hT l hi hpl G' mk hmk _ hmu hd bit hbit false _
        (sP _ (by simp)).2 (row _ (List.mem_append_right _ (by simp)))
    · exact rowP_sentence hadm.room hT l hi hpl G' mk hmk _ hmu hd bit hbit true _
        (sP _ (by simp)).2 (row _ (List.mem_append_right _ (by simp)))
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have hj' : j < g.keys.length := by rwa [List.length_zipIdx] at hj
    have hz : g.keys.zipIdx[j] = (g.keys.getD j (#[], {}), j) := by
      rw [List.getElem_zipIdx, Nat.zero_add, List.getD_eq_getElem]
    have sd := (sK _ hy).2
    rw [hz] at sd ⊢
    have hjl : j < l.parts.length := k1 ▸ hj'
    have hm' : A.m = l.parts.length := by
      show A.toPub.parts.length = _
      rw [hP]
      exact List.length_map _
    have hk := hKeys ⟨j, by rw [hm']; exact hjl⟩
    have hp : l.parts[j]? = some l.parts[j] := List.getElem?_eq_getElem hjl
    have hpk : l.paddingKey.toNat < 2 ^ l.d := by
      have h := hlo
      simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.2
    show readE (affAt G' homeA mk (g.keys.getD j (#[], {})).2) = readE (sumE
      (2 ^ (faceOfLkp (Wf.lookupOf id m l)).parts.getD j 0) fun k =>
        mulE ((Tensor.eq (g.keys.getD j (#[], {})).1.toList.reverse).entry k)
          (subE g.alpha (keyVec m l mat j k)))
    rw [← hv j]
    refine (key_iff_rdCl G' homeA mk g.alpha (A.v j) _ (k2 j hjl) (keyVec m l mat j) _
      (fun n _ => ?_) fun q hq => ?_).2 hk
    · rw [hK j _ hp, key_cut m _ _ _ (Leaves.rowsIn_of _ (List.length_map _) hfm
        (List.getElem_mem hjl)), read_keyVec m l mat j _ hp n, Leaves.read_padOf id m l zeroE hpk]
    · rw [hT.mask q.1 (mfOf_home G' homeA _ sd q hq), hmk q.1 (mfOf_home G' homeA _ sd q hq)]

end Johnson.RunOne.Law.TieDoneBack

#print axioms Johnson.RunOne.Law.TieDoneBack.rowA_zero
#print axioms Johnson.RunOne.Law.TieDoneBack.rowP_sentence
#print axioms Johnson.RunOne.Law.TieDoneBack.sentences_of_done
