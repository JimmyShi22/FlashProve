-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySendYes.lean: THE TRACER ON ROW 1.0, LEVEL 4: Left10's (Johnson/Top/Fire/Code/Row10At.lean) LARGEST FIELD, (yes): SendYes₀ (Johnson/RunOne/KeyRow10.lean): WHAT THE FIRST SENDING's YES GIVES OF THE RECORD: from the tables' book-keeping and last letter at border 0: those at border 1. BY send_laid | send_order (Johnson/Desc/Key/Laid/SendLaid.lean: what a yes of K1's own decideSend lays), carried through the seat (Johnson/Desc/Key/One.lean: sendIndexMasks).
OBJECT: shape₁ | free₁ at border 1 · USER: Left10.yes · LETTERS: F G at_ one R coll; N groups.
  idx_yes       PROVED: a yes of sendIndexMasks on two rounds IS a yes of decideSend at the state's record, and the state behind is written out
  Public10      FOUR PUBLIC PREMISES ON THE PLAN AND THE SEAT: planOkOwn at the place · the index masks' message is sampled · its one tree: the layout of that one message has one tree and seats it at (0, 0) · the table's seat at_ 0 is (0, 0)
  shape_send0   PROVED: the book-keeping at border 1
  free_send0    PROVED: the promise's last letter at border 1, at New := ShownAt F at_ 0
  sendYes₀      PROVED: SendYes₀ at every block whose decide and rounds are sendIndexMasks'
Nothing on soundness.
-/
import Johnson.RunOne.KeyRow10
import Johnson.RunOne.KeyBookStep
import Johnson.RunOne.KeyRow10Send
import Johnson.Desc.Key.Laid.SendLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.K1 (Par decideSend planOkOwn)
open VerifiableInference.Desc.Key.LaidW (SendLaid send_laid send_order)

theorem roundsFit_noDigest' : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by simp only [List.map_cons, roundsFit, drawsMarkedNonzeroHaveNonzeroWords, noDigest, roundsFit_noDigest' ds rs]

section
variable {β Cl : Type}

/-- The place's parameters. -/
abbrev parIdx (one : OneTime) (N : Pieces) (groups : List (List Nat)) : Par := sendingPar one N.idx "the index masks" #[one.indexMasks] groups

/-- **A yes of the key file's first sending, written out.** -/
theorem idx_yes (one : OneTime) (N : Pieces) (groups : List (List Nat)) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendIndexMasks one N groups : Block (ChainState β) Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ (ids : Array Nat) (d' : _root_.Desc.Plain.DState (Array Nat)) (i : Nat),
      decideSend (parIdx one N groups) s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂] = .ok (ids, d') ∧ ids[0]? = some i ∧
      s' = { s with d := withLoc ({ d' with loc := ids } : _root_.Desc.Plain.DState (Array Nat)) (), owed := none, sent := ids, idx := i } := by
  have h' : (((decideSend (parIdx one N groups) s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂]).map fun x =>
      ({ owed := none, held := { x.2 with loc := x.1 } } : K1.Owing (_root_.Desc.Plain.DState (Array Nat)))).map (fun y =>
        { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc })).bind (fun (s₁ : ChainState β) => (do
          let i ← named "the sending has left no number" s₁.sent[0]?
          pure { s₁ with idx := i } : Except String (ChainState β))) = .ok s' := h
  cases hd : decideSend (parIdx one N groups) s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂] with
  | error e => rw [hd] at h'; cases h'
  | ok x =>
    rw [hd] at h'
    have h2 : (do
        let i ← named "the sending has left no number" x.1[0]?
        pure { ({ s with d := withLoc ({ x.2 with loc := x.1 } : _root_.Desc.Plain.DState (Array Nat)) (), owed := none, sent := x.1 } : ChainState β) with idx := i } : Except String (ChainState β)) = .ok s' := h'
    cases hi : x.1[0]? with
    | none => rw [hi] at h2; cases h2
    | some i =>
      rw [hi] at h2
      exact ⟨x.1, x.2, i, rfl, hi, (Except.ok.inj h2).symm⟩

end

/-! ## What the yes lays, in the tables' own readers -/

/-- What row 1.0's block leaves of the first chain's state, where it began at an empty statement and book. -/
structure Sent0 (s s' : FirstState) : Prop where
  codes : s'.d.st.codes = s.d.st.codes
  idx : s'.idx = 0
  base : s'.base = s.base
  lin : s'.lin = s.lin
  size : s'.d.st.oracles.size = 1
  groups : s'.d.st.groups = s.d.st.groups
  trees : s'.d.book.trees.size = 1
  places : s'.d.book.place.size = 1
  place0 : s'.d.book.place[0]? = some (0, 0)
  msg0 : ∃ x, s'.d.st.oracles[0]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0
  order : Means.InOrder s'.d.st
  /-- the book stays in order -/
  step : VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots = true → VerifiableInference.Desc.Sound.bookStepB 0 s'.d.book s'.d.roots = true

/-- **Three public premises on the plan.** -/
structure Public10 (one : OneTime) (N : Pieces) (groups : List (List Nat)) : Prop where
  /-- the sending kind's own test on the plan, at the place -/
  plan : planOkOwn (parIdx one N groups) = true
  /-- the index masks' message is sampled -/
  sampled : one.indexMasks.shape.answers ≠ 0
  /-- the layout of that one message: one tree; the message is its first part -/
  lay : ∀ lay, layTrees one.codes #[one.indexMasks] = some lay → lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0

theorem sent0_of (one : OneTime) (N : Pieces) (groups : List (List Nat)) (Pb : Public10 one N groups) (s s' : FirstState) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (K1.rounds (parIdx one N groups)) [r₁, r₂] = true)
    (h : (sendIndexMasks one N groups : Block FirstState Claim).decide s [r₁, r₂] gs = .ok s')
    (h0 : s.d.st.oracles.size = 0) (ht : s.d.book.trees.size = 0) (hp : s.d.book.place.size = 0) (hI : Means.InOrder s.d.st) : Sent0 s s' := by
  obtain ⟨ids, d', i, hyes, hi, rfl⟩ := idx_yes one N groups s s' r₁ r₂ gs h
  have L := send_laid _ _ _ _ _ _ _ hyes
  have hs : (parIdx one N groups).sent = #[one.indexMasks] := rfl
  have hc : s.d.st.codes = one.codes := L.plan
  obtain ⟨lay, hlay, hseat⟩ := L.book
  have hlay' : layTrees one.codes #[one.indexMasks] = some lay := by
    rw [← hc, ← hs]
    exact hlay
  obtain ⟨l1, l2, l3⟩ := Pb.lay lay hlay'
  have hn : (parIdx one N groups).sent.size = 1 := rfl
  obtain ⟨x, hx, -, -, -, -, hx2⟩ := L.new 0 one.indexMasks rfl
  have hx' : d'.st.oracles[0]? = some x := by
    have e : (withLoc s.d (#[] : Array Nat)).st.oracles.size + 0 = 0 := by
      show s.d.st.oracles.size + 0 = 0
      omega
    rw [e] at hx
    exact hx
  have hpl := hseat.new 0 (by rw [hn]; omega)
  exact
    { codes := L.codes
      idx := by
        have e := L.idsAre
        rw [e] at hi
        have e0 : (withLoc s.d (#[] : Array Nat)).st.oracles.size = 0 := h0
        rw [hn, e0] at hi
        simpa using hi.symm
      base := rfl
      lin := rfl
      size := by
        have e := L.size
        rw [hn] at e
        show d'.st.oracles.size = 1
        have e0 : (withLoc s.d (#[] : Array Nat)).st.oracles.size = 0 := h0
        omega
      groups := L.groups
      trees := by
        have e := hseat.size
        show d'.book.trees.size = 1
        have e0 : (withLoc s.d (#[] : Array Nat)).book.trees.size = 0 := ht
        omega
      places := by
        have e := hseat.count
        rw [hn] at e
        show d'.book.place.size = 1
        have e0 : (withLoc s.d (#[] : Array Nat)).book.place.size = 0 := hp
        omega
      place0 := by
        have e0 : (withLoc s.d (#[] : Array Nat)).st.oracles.size + 0 = 0 := by
          show s.d.st.oracles.size + 0 = 0
          omega
        have e1 : (withLoc s.d (#[] : Array Nat)).book.trees.size = 0 := ht
        rw [e0, e1, l2, l3] at hpl
        exact hpl
      msg0 := ⟨x, hx', (hx2 Pb.sampled).1, by rw [(hx2 Pb.sampled).2]; exact Pb.sampled⟩
      order := (send_order (parIdx one N groups) s.debt (withLoc s.d (#[] : Array Nat)) d' r₁ r₂ ids Pb.plan hfit hyes hI : Means.InOrder d'.st)
      step := fun hb => (VerifiableInference.Desc.Sound.bookStep_iff 0 d'.book d'.roots).2
        (bookStep_of_seated 0 s.d.book d'.book _ _ lay _ s.d.roots d'.roots ((VerifiableInference.Desc.Sound.bookStep_iff 0 s.d.book s.d.roots).1 hb) hseat (L.roots lay hlay)) }

/-- What the tables' book-keeping at border 0 says of the state in front. -/
theorem front0 (one : OneTime) (s : FirstState) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0 s = true) :
    s.d.st.oracles.size = 0 ∧ s.d.st.groups.size = 0 ∧ s.d.book.trees.size = 0 ∧ s.d.book.place.size = 0 := by
  have ht : ties₁ one 0 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ sizesB at ht
  simp only [Bool.and_eq_true, beq_iff_eq, counts₁] at ht
  obtain ⟨⟨-, -⟩, ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩, -⟩, -⟩, -⟩⟩ := ht
  have a' : s.d.st.oracles.size = 0 := a
  exact ⟨a', b, c, by rw [d]; exact a'⟩

/-- **The book-keeping at border 1.** -/
theorem shape_send0 (one : OneTime) (s s' : FirstState) (H : Sent0 s s')
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 1 s' = true := by
  obtain ⟨-, g0, -, -⟩ := front0 one s h
  have ht : ties₁ one 0 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  obtain ⟨x, hx, hx1, hx2⟩ := H.msg0
  have h1 : s'.d.st.oracles[1]? = none := Array.getElem?_eq_none (by rw [H.size])
  have hstep := H.step
  refine (shape₁_iff _ _ _ _ _ _ _).2 ⟨?_, ?_⟩
  · show ties₁ one 1 s' = true
    unfold ties₁ tiesA moreB sizesB at ht ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, counts₁, done₁, H.codes, H.idx, H.base, H.lin, H.size, H.groups, H.trees, H.places] at ht ⊢
    simp_all
  · show core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 1 s' = true
    have e0 : sentB (plan₁ one) (readers₁ one) s' 0 = true := by
      show (match ((plan₁ one).orc 0).bind fun o => s'.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = true
      have e : (((plan₁ one).orc 0).bind fun o => s'.d.st.oracles[o]?) = some x := hx
      rw [e]
      simp [hx1, hx2]
    have e1 : sentB (plan₁ one) (readers₁ one) s' 1 = false := by
      show (match ((plan₁ one).orc 1).bind fun o => s'.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = false
      have e : (((plan₁ one).orc 1).bind fun o => s'.d.st.oracles[o]?) = none := h1
      rw [e]
    have e2 : ((readers₁ one).st s').groups.size = 0 := by
      show s'.d.st.groups.size = 0
      rw [H.groups]
      exact g0
    unfold core₁
    simp [e0, e1, e2]

/-- The book-keeping at two lookups, under a short name. -/
abbrev shape₁' (one : OneTime) (k : Nat) (s : FirstState) : Bool := shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k s

/-- **Behind the yes the statement has just one message.** -/
theorem size1_of_yes (one : OneTime) (N : Pieces) (groups : List (List Nat)) (Pb : Public10 one N groups)
    (b : Block FirstState Claim) (hd : b.decide = (sendIndexMasks one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parIdx one N groups))
    (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hf : roundsFit (held b : Block (Xi × FirstState) Claim).rounds rs = true)
    (hy : b.decide s (rs.map noDigest) gs = .ok s') (h1 : shape₁' one 0 s = true) (hI : Means.InOrder s.d.st) : s'.d.st.oracles.size = 1 := by
  have hf0 : roundsFit (K1.rounds (parIdx one N groups)) rs = true := hr ▸ hf
  have hlen := roundsFit_length _ _ hf0
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, -, c0, d0⟩ := front0 one s h1
  have hf' : roundsFit (K1.rounds (parIdx one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf0
  exact (sent0_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 c0 d0 hI).size

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

theorem pinned_behind0 : pinned (open₁ 2 1) = [0] := by decide

/-- **The promise's last letter at border 1.** -/
theorem free_send0 (hR : RecStays G) (hcoll : CollCell coll) (hat : at_ 0 = (0, 0)) (p : Xi) (s s' : FirstState) (y y' : Strs) (H : Sent0 s s')
    (Hy : StrsStay F at_ (open₁ 2 0) y y') (hN : ShownAt F at_ 0 y') (h : free₁ F G at_ one R coll 0 (p, s) y) : free₁ F G at_ one R coll 1 (p, s') y' := by
  obtain ⟨⟨r, hr, hn⟩, h2, -, -, -, -, -, -, h9, -, -⟩ := h
  refine ⟨⟨r, (hR p s s').trans hr, fun hc => hn (hcoll y y' r Hy.cell hc)⟩, h2, ?_, fun h18 => absurd h18 (by decide), ?_, fun h18 => absurd h18 (by decide), H.order, ?_, h9,
    fun h2 => absurd h2.1 (by decide), fun h18 => absurd h18 (by decide)⟩
  · intro k hk
    rw [pinned_behind0] at hk
    obtain rfl : k = 0 := by simpa using hk
    exact ⟨0, (0, 0), rfl, H.place0, hat⟩
  · intro j _ o _ x hx r' hr'
    exact H.order.samples o x hx r' hr'
  · intro j hj
    rw [pinned_behind0] at hj
    obtain rfl : j = 0 := by simpa using hj
    exact hN

/-- **(yes): WHAT THE FIRST SENDING's YES GIVES OF THE RECORD**, at every block whose decision and rounds are sendIndexMasks'. -/
theorem sendYes₀ (N : Pieces) (groups : List (List Nat)) (Pb : Public10 one N groups) (hR : RecStays G) (hcoll : CollCell coll) (hat : at_ 0 = (0, 0))
    (b : Block FirstState Claim) (hd : b.decide = (sendIndexMasks one N groups : Block FirstState Claim).decide)
    (hr : b.rounds = K1.rounds (parIdx one N groups)) :
    SendYes₀ F G at_ one R coll (ShownAt F at_ 0) b := by
  intro p s s' rs gs y y' hf hy Hy hN h1 h3
  rw [hr] at hf
  have hlen := roundsFit_length _ _ hf
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, -, c0, d0⟩ := front0 one s h1
  have hf' : roundsFit (K1.rounds (parIdx one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf
  have H := sent0_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 c0 d0 h3.2.2.2.2.2.2.1
  exact ⟨shape_send0 one s s' H h1, free_send0 F G at_ one R coll hR hcoll hat p s s' y y' H Hy hN h3⟩

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.idx_yes
#print axioms Johnson.RunOne.KeyRows1.sent0_of
#print axioms Johnson.RunOne.KeyRows1.shape_send0
#print axioms Johnson.RunOne.KeyRows1.size1_of_yes
#print axioms Johnson.RunOne.KeyRows1.free_send0
#print axioms Johnson.RunOne.KeyRows1.sendYes₀
