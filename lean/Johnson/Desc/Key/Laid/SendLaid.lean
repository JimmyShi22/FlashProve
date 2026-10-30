-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/SendLaid.lean: WHAT A YES OF K1's SENDING's DECISION
(Johnson/Desc/K1/Own.lean: decideSend) SAYS OF THE RECORD BEHIND, as one structure of plain facts.
Definitions, statements and proofs, over the laws: decideSend_iff (Johnson/Desc/K1/Law/Writes3.lean:
the record behind as one written term), decideSend_keeps (Johnson/Desc/K1/Law/KeepsOrder.lean) and
recvP_seat (Johnson/Desc/Book/BookFitsGround.lean) and recvP_roots
(Johnson/Desc/Book/BookNumbers.lean).
  outs_get        the i-th message behind a sending, with what the counts' test says of it.
  SendLaid P d d' ids : the numbers handed back · the codes, the groups, the opened columns and the
                  chain's own values as they were · every older message as it was · as many
                  messages more as were sent · EACH NEW MESSAGE: its shape is the notice's; in no
                  group; not spent; without an answer: no sample, no sample row; with answers:
                  sampled, as many sample rows as answers · the book: Seated · the count of roots:
                  as many more as the layout has trees.
  send_laid       a yes of decideSend gives it.
  send_order      with the plan's test and the rounds' fit: a statement in order stays in order:
                  decideSend_keeps, under this file's name for a caller's ease.
  sendLaid_irrefl where a message is sent SendLaid holds of no record and itself.
Limits. What a sample row IS (K1's sampleRow at the drawn seed) is not carried: see the
K1/Law files. Nothing on what a row means, on soundness or on hiding.
-/
import Johnson.Desc.K1.Law.KeepsOrder
import Johnson.Desc.Book.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes OnBytes.Params OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc (roundsFit)
open VerifiableInference.Desc.Book (Seated recvP_seat recvP_roots)
open VerifiableInference.Desc.K1

variable {L : Type}

/-- The i-th message behind a sending. -/
theorem outs_get (codes : Codes) (seeds : List (List E × E)) :
    ∀ (shapes : List OracleShape) (o : Nat) (ys : List E) (i : Nat) (s : OracleShape),
      fitB codes seeds.length shapes ys = true → shapes[i]? = some s →
      ∃ ys', (outs codes seeds o shapes ys)[i]? = some (wr codes seeds (o + i) s ys') ∧
        (s.answers ≠ 0 → s.answers ≤ seeds.length ∧ s.answers ≤ ys'.length)
  | [], _, _, _, _, _, h => by cases h
  | t :: l, o, ys, 0, s, hf, h => by
    obtain rfl : t = s := Option.some.inj h
    refine ⟨ys, rfl, fun h0 => ?_⟩
    unfold fitB at hf
    rw [if_neg h0] at hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    exact ⟨hf.1.1.1, hf.1.1.2⟩
  | t :: l, o, ys, i + 1, s, hf, h => by
    have hf' : fitB codes seeds.length l (ys.drop t.answers) = true := by
      unfold fitB at hf
      by_cases h0 : t.answers = 0
      · rw [if_pos h0] at hf
        rw [h0]
        exact hf
      · rw [if_neg h0] at hf
        simp only [Bool.and_eq_true] at hf
        exact hf.2
    obtain ⟨ys', a, b⟩ := outs_get codes seeds l (o + 1) (ys.drop t.answers) i s hf' h
    refine ⟨ys', ?_, b⟩
    rw [show o + (i + 1) = o + 1 + i by omega]
    exact a

/-- **What a yes of the sending's decision says of the record behind.** -/
structure SendLaid (P : Par) (d d' : DState L) (ids : Array Nat) : Prop where
  idsAre : ids = (Array.range P.sent.size).map (· + d.st.oracles.size)
  plan : d.st.codes = P.codes
  codes : d'.st.codes = d.st.codes
  groups : d'.st.groups = d.st.groups
  opened : d'.opened = d.opened
  loc : d'.loc = d.loc
  size : d'.st.oracles.size = d.st.oracles.size + P.sent.size
  /-- every older message is as it was -/
  older : ∀ o, o < d.st.oracles.size → d'.st.oracles[o]? = d.st.oracles[o]?
  /-- each new message -/
  new : ∀ (i : Nat) (n : OracleNotice), P.sent[i]? = some n →
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + i]? = some x ∧
    x.shape = n.shape ∧ x.groups = [] ∧ x.spentAsMask = false ∧
    (n.shape.answers = 0 → x.sampled = false ∧ x.sampleRows = #[]) ∧
    (n.shape.answers ≠ 0 → x.sampled = true ∧ x.sampleRows.size = n.shape.answers)
  /-- the book -/
  book : ∃ lay, layTrees d.st.codes P.sent = some lay ∧
    Seated d.book d'.book P.sent.size d.st.oracles.size lay
      (fun τ => P.gp.firstTree + (d.roots + τ)) (fun τ => .own (d.roots + τ))
  /-- the count of roots: as many more as the layout has trees -/
  roots : ∀ lay, layTrees d.st.codes P.sent = some lay → d'.roots = d.roots + lay.shapes.size

/-- **A YES OF THE SENDING's DECISION GIVES SendLaid.** -/
theorem send_laid (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    SendLaid P d d' ids := by
  obtain ⟨⟨_, hc, _, hok, hf⟩, hid, hd'⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  have hsome : (layTrees P.codes P.sent).isSome = true := by
    have := hok
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, Bool.and_eq_true] at this
    rw [← hc]
    -- The ground may ask Own.treesCan itself (as at Johnson/Desc/K1/Law/When.lean:208)
    exact (VerifiableInference.Desc.Own.treesCan_eq _ _) ▸ this.2.1
  obtain ⟨lay, hlay⟩ := Option.isSome_iff_exists.1 hsome
  have h5 : Ground.recvP P.gp.firstTree d P.sent =
      some ((Array.range P.sent.size).map (· + d.st.oracles.size),
        recvD P.gp.firstTree d P.sent lay) :=
    (recvP_iff _ _ _ _ _).2 ⟨hok, lay, by rw [hc]; exact hlay, rfl, rfl⟩
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hb : d' = put (recvD P.gp.firstTree d P.sent lay)
      (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)) := by
    rw [hd']
    simp [K1.behind, hlay]
  have hO : d'.st.oracles.toList = d.st.oracles.toList ++
      outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂) := by
    rw [hb]
    simp [put]
  have hget : ∀ j : Nat, d'.st.oracles[j]? = (d.st.oracles.toList ++
      outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[j]? := by
    intro j
    rw [← Array.getElem?_toList, hO]
  have hol : ∀ (shapes : List OracleShape) (o : Nat) (ys : List E),
      (outs P.codes (seedsOf P r₁) o shapes ys).length = shapes.length := by
    intro shapes
    induction shapes with
    | nil => intro _ _; rfl
    | cons s l ih =>
      intro o ys
      simp [outs, ih]
  refine ⟨hid, hc, by rw [hb]; rfl, by rw [hb]; rfl, by rw [hb]; rfl, by rw [hb]; rfl, ?_,
    fun o ho => ?_, fun i n hn => ?_, ?_, ?_⟩
  · rw [← Array.length_toList, hO, List.length_append, hol, Array.length_toList]
    simp [shapesOf]
  · rw [hget, List.getElem?_append_left (by rw [Array.length_toList]; exact ho),
      Array.getElem?_toList]
  · have hs : (shapesOf P)[i]? = some n.shape := by
      simp [shapesOf, hn]
    obtain ⟨ys', a, b⟩ := outs_get P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.size
      (answersIn r₂) i n.shape (by rw [hlen]; exact hf) hs
    refine ⟨wr P.codes (seedsOf P r₁) (d.st.oracles.size + i) n.shape ys', ?_, ?_⟩
    · rw [hget, List.getElem?_append_right (by rw [Array.length_toList]; omega),
        Array.length_toList, Nat.add_sub_cancel_left]
      exact a
    · by_cases h0 : n.shape.answers = 0
      · simp [wr, h0, fresh]
      · obtain ⟨b1, b2⟩ := b h0
        have hz := rowsOf_size P.codes (seedsOf P r₁) (d.st.oracles.size + i) n.shape ys' b1 b2
        simp [wr, h0, hz]
  · obtain ⟨_, lay', hl', hS⟩ := recvP_seat P.gp.firstTree d _ P.sent _ h5
    refine ⟨lay', hl', ?_⟩
    rw [hb]
    exact hS
  · intro lay₀ hl₀
    obtain ⟨lay', hl', hr⟩ := recvP_roots P.gp.firstTree d _ P.sent _ h5
    obtain rfl : lay' = lay₀ := Option.some.inj (hl'.symm.trans hl₀)
    rw [hb]
    exact hr

/-- With the plan's test and the rounds' fit a statement in order stays in order. -/
theorem send_order (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hB : planOkOwn P = true) (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (hI : Means.InOrder d.st) :
    Means.InOrder d'.st :=
  decideSend_keeps P owed d d' r₁ r₂ ids hB hfit h hI

/-- Where a message is sent SendLaid holds of no record and itself. -/
theorem sendLaid_irrefl (P : Par) (d : DState L) (ids : Array Nat) (hP : P.sent.size ≠ 0) :
    ¬ SendLaid P d d ids := fun h => by
  have := h.size
  omega

end VerifiableInference.Desc.Key.LaidW
