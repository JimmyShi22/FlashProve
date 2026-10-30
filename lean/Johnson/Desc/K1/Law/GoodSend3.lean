-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSend3.lean: **the law of a sending in the form of the rule of composition**
(Piece.GoodIn), general in the type of the carried record: a block whose yes is a yes of the kind's
decision, at its stretch of two written rounds, has what a block with a promise owes: at the written
count that bears the number of the place's bad seeds, the prover has lost towards: where the block
says yes, each new sampled message is sealed, and a witness behind is a witness in front.

Main names:
  Sealed     a message is sealed at a statement: the record holds, as its sample rows, just the
             kind's one row at a seed, and at that seed no two members of the library's list of the
             word sent have the same answer.
  IsSend     a block's yes on two rounds holds a yes of the kind's decision, and the statement that
             a reader takes off the carried record behind the block has the messages of the
             decision's, each with its shape, mark and sample rows.
  sendPiece  the piece: no round is laid behind; the extractor is the identity; the errors are the
             written counts that bear e at the round of the seeds and 0 at the round of the answers.
  send_goodIn  the law.
Letters: the conditions and relations at the two borders, with two premises at a yes: the condition
in front gives that behind, and a witness behind is one in front.

What is not claimed. One answer a message, and so one seed. The premises: the one Boolean on the
plan and the radii; the first written round draws as many elements as the place's point has
coordinates and a factor other than 0; the words are read off the oracles behind the block by a
function that reads, of the stretch's transcript, the first round's message alone. That a message is
in the list of the word sent is said nowhere. A block that refuses all has GoodIn too. Nothing on an
honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend2
import Johnson.Desc.K14.Law.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {L : Type}

/-- Behind a yes of the sending's decision, with the number of the elements drawn in the place of
the test of the rounds (seedIs_behind of SeedIs.lean spends of that test no more). -/
theorem seedIs_behind_len (P : Par) (rad : Nat → Nat) (owed : Option Nat) (d d' : DState L)
    (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hC : condPort P rad = true)
    (hlen : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1))
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) d'.st (d.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  have hT := cond_tie P rad hC k hk
  have h1 : 0 < P.seeds := one_le_seeds P k hk
  obtain ⟨sd, hsd, hz, hβ⟩ := hρ ⟨0, h1⟩
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  obtain ⟨t, ht⟩ : ∃ t, ys'[0]? = some t :=
    ⟨ys'[0]'(Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk') hy), List.getElem?_eq_getElem _⟩
  have hlen : sd.1.length = P.coordinates := cutSeeds_get _ _ _ _ sd hlen hsd
  have hb := bits_le_coordinates P k hk
  have e3 : seedAt P (bitsZ P.codes (shapeAt P k)) ρ =
      (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
    unfold seedAt ownSeeds
    exact dif_pos h1
  refine ⟨readE t, hc, _, sd.1, sd.2, t, hx, ?_, by simp [wr, hk'], ?_, ?_, rfl⟩
  · unfold wr
    split <;> rfl
  · have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    exact rowsOf_one _ _ _ _ _ hT.one sd t hsd ht
  · rw [e3]
    refine ⟨by rw [hlen]; exact hb, fun u => ?_, hβ⟩
    have hu : u.val < P.coordinates := Nat.lt_of_lt_of_le u.isLt hb
    show readL sd.1 u.val = pointOf (ρ ⟨0, h1⟩).1 u.val
    unfold pointOf
    rw [dif_pos hu]
    exact hz ⟨u.val, hu⟩

theorem outs_length (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List OracleShape) (o : Nat) (ys : List E), (outs codes seeds o l ys).length = l.length
  | [], _, _ => rfl
  | _ :: l, o, ys => by simp [outs, outs_length codes seeds l]

/-- A yes adds the place's messages to the statement's. -/
theorem size_behind (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    d'.st.oracles.size = d.st.oracles.size + (shapesOf P).length := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
    (answersIn r₂)).toArray.size = _
  simp [outs_length]

/-- A count along a one-to-one map. -/
theorem cnt_comp_le {α β : Type} [Finite α] [Finite β] (g : α → β) (hg : Function.Injective g)
    (Q : β → Prop) : cnt (fun a => Q (g a)) ≤ cnt Q := by
  unfold cnt
  exact Nat.card_le_card_of_injective (fun x : {a : α // Q (g a)} => (⟨g x.1, x.2⟩ : {b // Q b}))
    fun x y h => Subtype.ext (hg (congrArg Subtype.val h))

/-- **A message is sealed at a statement.** -/
def Sealed (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str) (St : Statement)
    (o : Nat) : Prop :=
  ∃ ρ y, SeedIs cs s St o ρ y ∧ ¬ (portOmZ cs s e).Clash f ρ

variable {T Cl W : Type} {F : Frame}

/-- **A block's yes holds a yes of the kind's decision.** stOf: the statement in a carried record.
What the block does to the statement behind the decision leaves the messages' number, shapes, marks
and sample rows. -/
def IsSend (P : Par) (stOf : T → Statement) (b : Block T Cl) : Prop :=
  ∀ s s' r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' →
    ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat),
      decideSend P owed d [r₁, r₂] = .ok (ids, d') ∧ SameMsgs d'.st (stOf s') ∧
        (stOf s').oracles.size = d'.st.oracles.size

/-- The piece that holds a block at the two written rounds of a sending. -/
noncomputable def sendPiece (b : Block T Cl) (base : Nat) (d₁ d₂ : RDT) (c e : Nat) :
    Piece (ckP .two) F T Cl W :=
  ⟨b, base, [d₁, d₂], [], fun _ _ w => w, (seedMaps d₁ d₂ c).err ((e, ()) : Nat × Unit)⟩

/-- **The law of a sending in the form of the rule of composition.** -/
theorem send_goodIn (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (h1 : P.seeds = 1)
    (b : Block T Cl) (stOf : T → Statement) (hS : IsSend P stOf b) (base : Nat) (d₁ d₂ : RDT)
    (hp : PlainDraws (Fmt.dsOf d₁.entry d₁.kind))
    (hE : nE (Fmt.dsOf d₁.entry d₁.kind) = P.coordinates + 1)
    (hP : nP (Fmt.dsOf d₁.entry d₁.kind) = 0)
    (hz : IsNZ (Fmt.dsOf d₁.entry d₁.kind) P.coordinates) (hl : d₁.entry.logN ≤ 64) (e : Nat)
    (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x → On' x)
    (hback : ∀ a τ x w, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      R' x w → R a w) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1)
          ((stOf x.1).oracles.size - (shapesOf P).length + k.val)) R R' := by
  have hne : Nonempty (Fin P.seeds) := ⟨⟨0, by omega⟩⟩
  refine goodIn_of_count_msg _ _ _ _ _ (seedRound d₁ P.coordinates) e
    (fun _ => (seedMaps d₁ d₂ P.coordinates).carry)
    (fun _ => (seedMaps d₁ d₂ P.coordinates).fits (seedMaps_ok d₂ hp hE hP hz hl) _)
    (fun a m z => BadPort P rad (fIn a.2 m) (fun _ => z)) ?_ ?_
  · intro a m _
    refine Nat.le_trans (cnt_comp_le (fun z (_ : Fin P.seeds) => z) (fun x y h => ?_)
      (BadPort P rad (fIn a.2 m))) (Nat.le_trans (badPort_count P rad hC _) he)
    exact congrFun h hne.some
  · intro a τ x ha hx
    have ht := Desc.K14.Law.piece_tests _ a τ x hx
    simp only [sTests, Bool.and_eq_true] at ht
    have hpass := seedMaps_pass d₁ d₂ P.coordinates τ ht.1.1
    obtain ⟨hx2, gs, hdec⟩ := Desc.K14.Law.piece_yes _ a τ x hx
    refine ⟨_, (seedMaps d₁ d₂ P.coordinates).tr_of_pass τ hpass, fun hgood => ?_⟩
    refine ⟨⟨hkeep a τ x ha hx, fun k hk => ?_⟩, fun w hw => hback a τ x w ha hx hw⟩
    obtain ⟨m₁, c₁, m₂, c₂, ⟨⟩⟩ := τ
    have hdec' : b.decide a.1 [noDigest (shownAt d₁ m₁ c₁), noDigest (shownAt d₂ m₂ c₂)] gs =
        .ok x.1 := hdec
    obtain ⟨L, d, d', owed, ids, hyes, hsame, e2⟩ := hS _ _ _ _ _ hdec'
    have hread := reads_shown P h1 d₁ hE hz m₁ c₁
    have hlen : ((noDigest (shownAt d₁ m₁ c₁)).drawn.elems.map E.ofTriple).length =
        P.seeds * (P.coordinates + 1) := by
      have hmap := rvOf_els (toRD d₁) (msgRD d₁ m₁) c₁
      have := congrArg List.length hmap
      rw [List.length_map, elemsV_length] at this
      rw [List.length_map, h1, Nat.one_mul]
      exact this.trans hE
    obtain ⟨y, hy⟩ := seedIs_behind_len P rad owed d d' _ _ ids hC hlen hyes _ hread k hk
    have hsize := size_behind P owed d d' _ _ ids hyes
    have hidx : (stOf x.1).oracles.size - (shapesOf P).length + k.val =
        d.st.oracles.size + k.val := by
      rw [e2, hsize]
      omega
    rw [hidx]
    refine ⟨_, y, hy.travels hsame, fun hcl => hgood ⟨k, hk, ?_⟩⟩
    rw [hx2, hf] at hcl
    exact hcl

/-! ## Tries -/

/-- Without an answer the counts fit only where no message is sampled. -/
theorem fitB_nil (codes : Codes) (n : Nat) : ∀ l : List OracleShape, fitB codes n l [] = true →
    ∀ s ∈ l, s.answers = 0
  | [], _, _, hs => absurd hs (List.not_mem_nil)
  | x :: l, h, s, hs => by
    unfold fitB at h
    by_cases h0 : x.answers = 0
    · rw [if_pos h0] at h
      rcases List.mem_cons.1 hs with rfl | hs
      · exact h0
      · exact fitB_nil codes n l h s hs
    · rw [if_neg h0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_nil] at h
      exact absurd (Nat.le_zero.1 h.1.1.2) h0

/-- **A block that says yes to all is no sending**, at a place with a sampled message: on a round
without an answer the kind's decision refuses. -/
theorem yesAll_not_send (P : Par) (stOf : T → Statement) (b : Block T Cl) (s s' : T)
    (hb : ∀ rs gs, b.decide s rs gs = .ok s') (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) : ¬ IsSend P stOf b := by
  intro h
  obtain ⟨L, d, d', owed, ids, hyes, _, _⟩ :=
    h s s' ⟨[], ⟨[], [], [], none⟩⟩ ⟨[], ⟨[], [], [], none⟩⟩ [] (hb _ _)
  obtain ⟨⟨_, _, _, _, hfit⟩, _, _⟩ := (decideSend_iff P owed d d' _ _ ids).1 hyes
  exact hk (fitB_nil _ _ _ hfit _ (List.getElem_mem k.isLt))

/-- At a statement without a message nothing is sealed. -/
theorem not_sealed_empty (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str)
    (St : Statement) (o : Nat) (h : St.oracles[o]? = none) : ¬ Sealed cs s e f St o := by
  rintro ⟨_, _, ⟨_, x, _, _, _, hx, _⟩, _⟩
  rw [h] at hx
  cases hx

end VerifiableInference.Desc.K1
