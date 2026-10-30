-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SendPQuiet.lean: no soundness is claimed.
The sending that is written over the verifier program's own functions (Desc.Plain.sendP at the plain ground, Johnson/Desc/Ground/Calls.lean) keeps every relation R on statements that the eight quiet functions keep (GroundQuiet R) and that the admitting of a sample keeps where the rows handed in are on the message (K1.AdmitOn R): with no premise on a plan, on the codes or on the announcements: an accept of sendP is enough.
sendP_keepsAll (Johnson/Top/H0/Tw/K2C/KeepsWhole.lean) has the like under GroundKeeps R, whose field «admit» asks R at any rows; kind K1's sendP_inOrder (K1/Law/KeepsOrder2.lean: neither the name nor the file is in this library) has one property under the tests on a plan and «every code's message length is a power of two».
  seeds_len · le_foldl_max · mapM_zip     three small facts
  rowsFor_on      the rows that rowsFor makes are on the message (rowOn_form, FormOn.lean)
  Ready …         what the loop asks of its list: each entry's message is there with that shape, has a row, and every seed's point has its cube's coordinates
  sampleLoop_rel  the loop keeps R
  **sendP_rel**   sendP groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d') → R d.st d'.st
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.FormOn
import Johnson.Desc.K1.Quiet
import Johnson.Desc.Own.SendAgree
import Johnson.Desc.GrowsGround
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Desc.K1.Law.Writes3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K1
open VerifiableInference.Desc.Ground (GroundQuiet)
open VerifiableInference.Desc.First.K2 (optBindB)

theorem seeds_len (bits : Nat) : ∀ (n : Nat) (l : List E) (seeds : List SampleSeed),
    Own.seedsMade bits n l = some seeds → ∀ sd ∈ seeds, sd.z.length = bits
  | 0, [], seeds, h => by
    simp only [Own.seedsMade, Option.some.injEq] at h
    subst h
    intro sd hsd
    cases hsd
  | 0, _ :: _, seeds, h => by simp [Own.seedsMade] at h
  | n + 1, l, seeds, h => by
    unfold Own.seedsMade at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      intro sd hsd
      rcases List.mem_cons.1 hsd with rfl | hsd
      · show (l.take bits).length = bits
        have e := congrArg List.length hd
        rw [List.length_drop, List.length_cons] at e
        rw [List.length_take]
        omega
      · exact seeds_len bits n rest t ht sd hsd

theorem le_foldl_max {α : Type} (f : α → Nat) : ∀ (l : List α) (b : Nat),
    b ≤ l.foldl (fun b s => max b (f s)) b ∧ ∀ s ∈ l, f s ≤ l.foldl (fun b s => max b (f s)) b
  | [], b => ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | a :: l, b => by
    obtain ⟨h1, h2⟩ := le_foldl_max f l (max b (f a))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 s hs

theorem mapM_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ x ∈ l.zip r, f x.1 = some x.2
  | [], r, _ => by simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    intro x hx
    rw [List.zip_cons_cons] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact mapM_zip f l r' hr' x hx

/-- The rows that `rowsFor` makes are on the message. -/
theorem rowsFor_on (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (hs : 0 < x.shape.mainRows + x.shape.maskRows) (seeds : List SampleSeed)
    (hz : ∀ sd ∈ seeds, (Send.cube S.codes x.shape).bits ≤ sd.z.length) :
    ∀ (is : List Nat) (ys : List E) (acc rows : Array OnBytes.Row) (ys' : List E),
      rowsFor S.codes x.shape o seeds is ys acc = some (rows, ys') →
      (∀ r ∈ acc.toList, Means.RowOn S o r) → ∀ r ∈ rows.toList, Means.RowOn S o r
  | [], ys, acc, rows, ys', h, ha => by
    simp only [rowsFor, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ha
  | _ :: _, [], acc, rows, ys', h, _ => by simp [rowsFor] at h
  | i :: is, y :: ys, acc, rows, ys', h, ha => by
    simp only [rowsFor] at h
    split at h
    · cases h
    · rename_i seed hseed
      split at h
      · cases h
      · rename_i row hrow
        refine rowsFor_on S o x hx hs seeds hz is ys _ rows ys' h fun r hr => ?_
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact ha r hr
        · rw [Own.formMade_eq] at hrow
          exact rowOn_form S o x hx seed.z seed.beta i y row hrow hs
            (hz seed (List.mem_of_getElem? hseed))

/-- What the loop asks of its list. -/
def Ready (S : Statement) (seeds : List SampleSeed) (l : List (Nat × OracleShape)) : Prop :=
  ∀ e ∈ l, ∃ x, S.oracles[e.1]? = some x ∧ x.shape = e.2 ∧
    0 < e.2.mainRows + e.2.maskRows ∧ ∀ sd ∈ seeds, (Send.cube S.codes e.2).bits ≤ sd.z.length

theorem Ready.grows {S S' : Statement} {seeds : List SampleSeed} {l : List (Nat × OracleShape)}
    (h : Ready S seeds l) (g : Grows S S') : Ready S' seeds l := fun e he => by
  obtain ⟨x, h1, h2, h3, h4⟩ := h e he
  obtain ⟨x', k1, k2⟩ := g.2.2 e.1 x h1
  exact ⟨x', k1, k2.1.trans h2, h3, by rw [g.1]; exact h4⟩

variable {L : Type} {R : Statement → Statement → Prop}

/-- The loop keeps R. -/
theorem sampleLoop_rel (H : GroundQuiet R) (hA : AdmitOn R) {p : GPar} {seeds : List SampleSeed} :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      Ready d.st seeds l →
      sampleLoop groundG p d.st.codes seeds l ys d = some (d', left) → R d.st d'.st
  | [], ys, d, d', left, _, h => by
    simp only [sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact H.refl _
  | (o, s) :: l, ys, d, d', left, hr, h => by
    simp only [sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' hrows
      split at h
      · cases h
      · rename_i d₁ ha
        obtain ⟨x, h1, h2, h3, h4⟩ := hr (o, s) List.mem_cons_self
        have h2' : x.shape = s := h2
        subst h2'
        have hon := rowsFor_on d.st o x h1 h3 seeds h4 _ ys #[] rows ys' hrows (by simp)
        have ha' : Ground.admitP d o rows = some d₁ := ha
        have g := Ground.admitP_grows d d₁ o rows ha'
        have hr' : Ready d₁.st seeds l :=
          Ready.grows (fun e he => hr e (List.mem_cons_of_mem _ he)) g
        rw [← g.1] at h
        exact H.trans (hA d d₁ o rows ha' hon) (sampleLoop_rel H hA l ys' d₁ d' left hr' h)

/-- What the receiving has entered has a row. -/
theorem recv_rows {ft : Nat} {d d₁ : DState L} {sent : Array OracleNotice} {ids : Array Nat}
    (h : Ground.recvP ft d sent = some (ids, d₁)) :
    ∀ o ∈ ids.toList, ∀ x, d₁.st.oracles[o]? = some x →
      0 < x.shape.mainRows + x.shape.maskRows := by
  obtain ⟨hok, lay, -, rfl, rfl⟩ := (recvP_iff ft d d₁ sent ids).1 h
  have h2 : (Ground.recvL d.st d.book sent).all (·.2) = true := hok
  unfold Ground.recvL Ground.sentL at h2
  simp only [List.cons_append, List.nil_append, List.all_cons, Bool.and_eq_true] at h2
  have hall := Array.all_eq_true_iff_forall_mem.1 h2.1
  intro o ho x hx
  simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at ho
  obtain ⟨k, hk, rfl⟩ := ho
  have hx' : (d.st.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[
      k + d.st.oracles.size]? = some x := hx
  rw [Array.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel, Array.getElem?_map,
    Array.getElem?_eq_getElem hk] at hx'
  have e : ({ shape := sent[k].shape } : OnBytes.Oracle) = x := Option.some.inj hx'
  rw [← e]
  have hf := hall sent[k] (Array.getElem_mem hk)
  unfold Own.sentShapeFits at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact hf.1.1.1

/-- **An accept of the sending keeps R.** -/
theorem sendP_rel (H : GroundQuiet R) (hA : AdmitOn R) {p : GPar} {own : Bool} {d d' : DState L}
    {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {sd an : List E} {need : Nat}
    (h : sendP groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d')) : R d.st d'.st := by
  unfold sendP at h
  obtain ⟨⟨ids', d₁⟩, h1, h⟩ := optBindB h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := optBindB h
  obtain ⟨seeds, hse, h⟩ := optBindB h
  obtain ⟨an', _, h⟩ := optBindB h
  have h1' : Ground.recvP p.firstTree d sent = some (ids', d₁) := h1
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBindB h
    dsimp only at h
    split at h
    · cases h
      refine H.trans (H.recv _ _ _ _ _ h1') (sampleLoop_rel H hA _ _ _ _ _ (fun e he => ?_) h2)
      have hm := mapM_zip _ _ _ hsh e he
      obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 hm
      obtain ⟨he1, he2⟩ := List.of_mem_zip he
      refine ⟨x, hx, hxs, ?_, fun s hs => ?_⟩
      · rw [← hxs]
        exact recv_rows h1' e.1 (List.mem_of_mem_filter he1) x hx
      · rw [seeds_len _ _ _ _ hse s hs]
        exact (le_foldl_max (fun s => (Send.cube d₁.st.codes s).bits) shapes 0).2 e.2 he2
    · cases h
  · cases h

end ToldDesc

#print axioms ToldDesc.sendP_rel
#print axioms ToldDesc.rowsFor_on
#print axioms ToldDesc.sampleLoop_rel
