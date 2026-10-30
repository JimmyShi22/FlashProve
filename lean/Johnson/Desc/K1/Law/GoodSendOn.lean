-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendOn.lean: the law of a sending whose block goes on (GoodSendOpen.lean),
for a block that is a sending of the place P only at the records inside a fence: a block that makes
its announcements out of the carried record (and tests them against no number of the place) holds a
yes of the place's sending only where the record in front has the place's announcements and codes.
And what the block does behind the sending need leave the SAMPLED messages alone (SmpStay), which
every plain function of the ground does.

Main names:
  IsSendOn     at a record inside the fence, a block's yes on a first round and whatever follows
               holds a yes of the kind's decision on that first round and some second; the
               statement behind the block has that decision's codes and sampled messages; a reader
               of the record behind returns the number of the first new message.
  send_goodIn_on   the law, with letters at the borders; the condition in front gives the fence.
  send_gives_on    the law as one lost game at a record inside the fence.
  isSendOn_of      the class without a fence (IsSendOpen) is in it, at every fence.
  isSendOn_of_sendP   every block whose yes, inside the fence, holds a yes of sendP at the place's
               numbers, announcements and codes.
  yesAll_not_sendOn   a try.
The proofs of the two laws are those of send_goodIn_open and send_gives_open, made from them by
program: three places turn.

What is not claimed. A FENCE THAT NO RECORD MEETS MAKES THE CLASS FREE AND THE LAW IDLE: the law is
worth what the condition in front is worth; that a run's records are inside the fence is owed by
whoever holds the chain in front of the block. The errors are 0 at the later rounds. One answer a
message. No block of another kind is shown here to be in the class. Nothing on soundness of a
protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SealStays
import Johnson.Desc.K1.Law.GoodSendOpenP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {T Cl W : Type} {F : Frame}

/-- **Inside the fence a block's yes holds a yes of the kind's decision on its first round and some
second.** -/
def IsSendOn (P : Par) (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop)
    (b : Block T Cl) : Prop :=
  ∀ s s' r₁ rs gs, Fn s → b.decide s (r₁ :: rs) gs = .ok s' →
    ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat) (r₂ : Fmt.RoundView),
      decideSend P owed d [r₁, r₂] = .ok (ids, d') ∧ SmpStay d'.st (stOf s') ∧
        first s' = d.st.oracles.size

/-- **The law of a sending whose block goes on, inside a fence.** -/
theorem send_goodIn_on (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop) (hS : IsSendOn P stOf first Fn b)
    (base : Nat)
    (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ,
      fOf ((openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.imp y τ) =
        fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (hFn : ∀ a, On a → Fn a.1) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a →
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ = some x →
      On' x)
    (hback : ∀ a τ x w, On a →
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ = some x →
      R' x w → R a w) :
    (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1) (first x.1 + k.val))
      R R' := by
  have h1 := seeds_one P rad hC
  obtain ⟨hp, hE, hP, hz, hl⟩ := seed_draws P h1 d₁ he₁ hk₁
  have hne : Nonempty (Fin P.seeds) := ⟨⟨0, by omega⟩⟩
  refine goodIn_of_count_msg _ _ _ _ _ (seedRound d₁ P.coordinates) e
    (fun _ => (seedMapsL d₁ ds P.coordinates).carry)
    (fun _ => (seedMapsL d₁ ds P.coordinates).fits (seedMapsL_ok ds hp hE hP hz hl) _)
    (fun a m z => BadPort P rad (fIn a.2 m) (fun _ => z)) ?_ ?_
  · intro a m _
    refine Nat.le_trans (cnt_comp_le (fun z (_ : Fin P.seeds) => z) (fun x y h => ?_)
      (BadPort P rad (fIn a.2 m))) (Nat.le_trans (badPort_count P rad hC _) he)
    exact congrFun h hne.some
  · intro a τ x ha hx
    have ht := Desc.K14.Law.piece_tests _ a τ x hx
    simp only [sTests, Bool.and_eq_true] at ht
    have hpass := seedMapsL_pass d₁ ds P.coordinates τ ht.1.1
    obtain ⟨hx2, gs, hdec⟩ := Desc.K14.Law.piece_yes _ a τ x hx
    refine ⟨_, (seedMapsL d₁ ds P.coordinates).tr_of_pass τ hpass, fun hgood => ?_⟩
    refine ⟨⟨hkeep a τ x ha hx, fun k hk => ?_⟩, fun w hw => hback a τ x w ha hx hw⟩
    obtain ⟨m₁, c₁, τ'⟩ := τ
    have hdec' : b.decide a.1 (noDigest (shownAt d₁ m₁ c₁) ::
        (rvT (ckP .two) ds τ' ++ back).map noDigest) gs = .ok x.1 := hdec
    obtain ⟨L, d, d', owed, ids, r₂, hyes, hold, hfirst⟩ := hS _ _ _ _ _ (hFn a ha) hdec'
    have hread := reads_shown P h1 d₁ hE hz m₁ c₁
    have hlen : ((noDigest (shownAt d₁ m₁ c₁)).drawn.elems.map E.ofTriple).length =
        P.seeds * (P.coordinates + 1) := by
      have hmap := rvOf_els (toRD d₁) (msgRD d₁ m₁) c₁
      have := congrArg List.length hmap
      rw [List.length_map, elemsV_length] at this
      rw [List.length_map, h1, Nat.one_mul]
      exact this.trans hE
    obtain ⟨y, hy⟩ := seedIs_behind_len P rad owed d d' _ _ ids hC hlen hyes _ hread k hk
    rw [hfirst]
    refine ⟨_, y, hy.stays hold, fun hcl => hgood ⟨k, hk, ?_⟩⟩
    rw [hx2, hf] at hcl
    exact hcl

/-- **The same as one lost game, with the sample read off the statement**: to be joined, at the sum
of the errors, to the law that the block has on its later rounds. -/
theorem send_gives_on (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop) (hS : IsSendOn P stOf first Fn b)
    (base : Nat)
    (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ,
      fOf ((openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.imp y τ) =
        fIn y τ.1) (a : T × F.E.Str) (ha : Fn a.1) :
    Doomed (uLT (ckP .two) (d₁ :: ds))
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).err fun τ =>
        ∀ x, (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ =
            some x →
          ∀ k, sampledAt P k → ∃ z,
            smpAt P.codes (shapeAt P k) (rad k.val) (stOf x.1) (first x.1 + k.val) = some z ∧
            ¬ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (fOf x.2 k) z.1 := by
  have g := send_goodIn_on (W := W) (F := F) P rad hC b stOf first Fn hS base d₁ ds back he₁ hk₁ e
    he fOf fIn hf (fun x => Fn x.1) (fun _ => True) (fun _ h => h) (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  refine Doomed.mono _ _ (fun τ hτ x hx k hk => ?_) (g a ha)
  obtain ⟨ρ, y, hs, hc⟩ := (hτ x hx).1.2 k hk
  obtain ⟨z, h1, h2, _⟩ := smpAt_of _ _ (rad k.val) _ _ ρ y (cond_tie P rad hC k hk) hs
  exact ⟨z, h1, fun hcl => hc ((clash_val _ _ z.1 ρ h2).1 hcl)⟩

/-- The class without a fence is in it. -/
theorem isSendOn_of (P : Par) (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop)
    (b : Block T Cl) (h : IsSendOpen P stOf first b) : IsSendOn P stOf first Fn b := by
  intro s s' r₁ rs gs _ hy
  obtain ⟨L, d, d', owed, ids, r₂, h1, h2, h3⟩ := h s s' r₁ rs gs hy
  exact ⟨L, d, d', owed, ids, r₂, h1, smpStay_of_old h2, h3⟩

/-- **Every block that, inside the fence, calls sendP at the place's numbers.** -/
theorem isSendOn_of_sendP (P : Par) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop) (b : Block T Cl)
    (h : ∀ s s' r₁ rs gs, Fn s → b.decide s (r₁ :: rs) gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (gp : GPar) (sent : Array OracleNotice) (own : Bool)
        (r₂ : Fmt.RoundView) (ids : Array Nat) (sd an : List E) (need : Nat),
        sendP groundG gp own d sent r₁ r₂ = some (ids, sd, an, need, d') ∧ gp = P.gp ∧
          sent = P.sent ∧ d.st.codes = P.codes ∧ SmpStay d'.st (stOf s') ∧
          first s' = d.st.oracles.size) :
    IsSendOn P stOf first Fn b := by
  intro s s' r₁ rs gs hs hy
  obtain ⟨L, d, d', gp, sent, own, r₂, ids, sd, an, need, h1, rfl, rfl, hc, h2, h3⟩ :=
    h s s' r₁ rs gs hs hy
  exact ⟨L, d, d', none, ids, cutTo P r₂,
    (decide_of_sendP P own d d' r₁ r₂ ids sd an need hB hl hc h1).1, h2, h3⟩

/-- **A block that says yes to all is not in the class**, at a place with a sampled message and a
fence that holds the record. -/
theorem yesAll_not_sendOn (P : Par) (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop)
    (b : Block T Cl) (s s' : T) (hs : Fn s) (hb : ∀ rs gs, b.decide s rs gs = .ok s')
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) : ¬ IsSendOn P stOf first Fn b := by
  intro h
  obtain ⟨L, d, d', owed, ids, r₂, hyes, _, _⟩ :=
    h s s' ⟨[], ⟨[], [], [], none⟩⟩ [] [] hs (hb _ _)
  obtain ⟨⟨_, _, hnz, _, _⟩, _, _⟩ := (decideSend_iff P owed d d' _ _ ids).1 hyes
  have h1 := one_le_seeds P k hk
  obtain ⟨n, hn⟩ : ∃ n, P.seeds = n + 1 := ⟨P.seeds - 1, by omega⟩
  have hm : (([] : List E), zeroE) ∈ seedsOf P ⟨[], ⟨[], [], [], none⟩⟩ := by
    unfold seedsOf
    rw [hn]
    simp [cutSeeds]
  have := hnz _ hm
  exact absurd this (by decide)

end VerifiableInference.Desc.K1
