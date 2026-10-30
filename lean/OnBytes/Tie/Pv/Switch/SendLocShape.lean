-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Switch/SendLocShape.lean: the entries SEND seed and LOC stand side by side in the
list of the frame's rounds of a proof file's first chain, from every group but the first onward.
Under four conditions on its letters, and if the plan's message has a root, the typed block of a
sending with a rider, followed by the round of positions, has the rounds of these two entries, in
the sense of ShapeIsAll. Definitions, statements and proofs.

Background. A proof file's first chain goes group by group. From the second group on, the last one
too, the planner's routine reqPlanFrom (OnBytes/Params/DeriveReq.lean) sends the group's oracle
messages without a round of their own for the answers to their samples, and then plans the round of
positions at which the group before is opened; that round also takes the answers in. Among the
messages sent is the fresh mask of the group's own fold, which has no sample. The typed block has a
place for an oracle message that is sent and not sampled, and calls it the rider; it is meant for
that mask. It is not one of the `riders` of reqSend, of which there are none from the second group
on. OnBytes/Plan/PlanListsReq.lean lists the rounds that reqPlanFrom adds, given lists for the
sub-proofs' rounds (reqListFrom, runs_reqPlanFrom). A round is described there by a RoundSpec
(OnBytes/Params/PlanningLaws.lean). The two rounds are sendSeed s o roots
(OnBytes/Params/PlanListsProx.lean) and locRound s c g b 0 a, with o the sampled oracle messages,
roots the number of trees of the prover's message (treesOf, which may give none), g the group
before, and a = s.samples * o.length answers in b = 24 * a bytes.

What the file does. It lays a typed block beside the two rounds: `Cb.Pv.SendLocRide.R z`
(Cb/Pv/Switch/SendLocRide.lean), for every value z of its record of types, codes and numbers (its
letters). The block has two rounds. In the first the prover sends the rider's word and the words of
a family of oracle messages (Sig, Cb/Ld/LdSig.lean), and the verifier draws one seed for all members
of the family (Sig.Seeds, Cb/Ld/LdSendFam.lean). In the second the prover sends the answers, and the
verifier draws positions of the word that is open from before. That typed rounds are the rounds of a
list of entries, one by one, for entries of every kind but two that are told there, is said by
`ShapeIsAll` (OnBytes/G4/RoundIsAll.lean).

Main names:
  `sampledAt`, `reqList_sendLoc`: the list of the frame's rounds (reqListFrom), taken from a group
    onward that is not the first, begins with the round REPLY, if the first link that is left has
    plain scalars, and then has sendSeed and locRound side by side, at the sampled messages
    sampledAt, if treesOf gives a number.
  `sendLoc_plains`, `sendLoc_places`, `sendLoc_draws`: the two rounds' plain parts, oracle positions
    and verifier's messages, as the library's types have them.
  `largestCube o`: the largest number of variables of a sample's cube among the messages o, in the
    words of sendSeed; 0 if there is no message.
  `SendLocFits z samples cube answers t logN`: the four conditions on the letters z (seeds, place,
    answers, positions); each is told at its field.
  `noPlain`, `answersPlain`, `positionsDraw`: three bijections: a message of a single value is no
    element of E and none of F; the answers beside a single value are k elements of E and none of F;
    t positions are a draw of t positions and nothing else (DrawSet).
  `sendLoc_shape`: if roots is not 0, and under SendLocFits at samples = s.samples,
    cube = largestCube o, answers = s.samples * o.length, t = baseCount s c g and
    logN = g.main.logN, the block's shape has the rounds of the entries of sendSeed s o roots and of
    locRound s c g (24 * answers) 0 answers.
  `sendLoc_listed`: the same at the setting, the scope, the messages and the group at which
    reqList_sendLoc has the two descriptions.

Limits.
 - No statement here says that a value of the letters meets SendLocFits, that it can be met together
   with the block's own condition (SendLocRide.OK), or that a typed protocol of this library has
   this block at this place.
 - SendLocFits is the conclusion, read on the letters. The theorem adds of which letters the two
   merged rounds are made (sendLoc_plains, sendLoc_places, sendLoc_draws), that the second has no
   oracle position, and that the entries' numbers are those at which SendLocFits is asked.
 - SendLocFits ties totals only: not that the family has o.length members, not a member's own cube
   or number of answers. Of the cubes only the largest shows, through the size of the seed.
 - No statement here or in Cb/Pv/Switch/SendLocRide.lean says that the fold which follows takes the
   rider as its mask.
 - The same block fits sendSeed s o roots for every roots but 0. Of the first prover's message
   nothing is tied but that its plain part has a single value and that it has an oracle position:
   not the number of trees, not its 32 * roots bytes, not the size of the words, not their order. In
   the merged message the rider comes first; in the programs' message the mask stands last.
 - That roots is not 0 is a premise on a number of the plan. No statement here shows it of the
   number of trees.
 - ShapeIsAll counts. Of an entry's eleven numbers it reads seven. msg is tied through a bijection
   and an equation with two numbers that are only said to exist; the five numbers of the draw share
   one bijection; neither bijection is chosen anywhere; of roots it says only none or some. It ties
   neither the name nor count, work, answers and rows. What it lets through is told in the head of
   OnBytes/G4/RoundIsAll.lean.
 - E is any finite field and F any type. What a round is proved to determine of these numbers, and
   over which sizes, is in the laws of OnBytes/G4/RoundIsAll.lean.
 - runs_reqPlanFrom shows which rounds reqPlanFrom adds where it returns a state, under a premise on
   the sub-proofs' routines (SubRuns) that this library does not prove of the model's sub-proofs. No
   statement here joins it with reqList_sendLoc, and none shows that reqListFrom from a group onward
   is a stretch of the whole chain's list (firstChainList). Where treesOf gives none, the list has
   locRound alone, and the plan is refused.
 - At baseCount s c g = 0 the planner refuses, and the statements here speak of a draw of no
   position.
 - Nothing on the first group's sending, which has a round of its own for the answers and no round
   of positions; on the sendings of a link's later moments; or on a sending inside a proximity test.
 - Nothing on the two rounds' errors: the block's (SendLocRide.errs) are not compared with the
   plan's bounds here.
-/
import OnBytes.Plan.PlanListsReq
import OnBytes.G4.RoundIsAll
import Cb.Pv.Switch.SendLocRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open Iop Cb OnBytes OnBytes.G4 OnBytes.Params OnBytes.Plan

/-! ### The plan's side -/

/-- The sampled oracle messages of the sending of group number l, not the first, in the words of
reqListFrom. -/
def sampledAt (y : ProofSized) (l : ℕ) (g : ReqGroup) (links : List ReqLink) : List SampleSize :=
  reqSampled y.codes (membersOf y l g ((links.head?.map (·.messages)).getD []))
    (if links.head?.isSome then y.link.group else y.last.first) y.batch.own.first 0

/-- The list of the frame's rounds, taken from a group onward that is not the first, begins with the
round REPLY, if the first link that is left has plain scalars, and then has sendSeed and locRound
side by side, if treesOf gives a number. -/
theorem reqList_sendLoc (y : ProofSized) (L : ℕ → ℕ → List RoundSpec) (l : ℕ) (g : ReqGroup)
    (gs : List ReqGroup) (links : List ReqLink) (open_ : List ℕ) (before : GroupSize) (roots : ℕ)
    (hl : l ≠ 0)
    (ht : treesOf y.codes (membersOf y l g ((links.head?.map (·.messages)).getD [])).toArray =
      some roots) :
    ∃ rest, reqListFrom y L l (g :: gs) links open_ before =
      (if (links.head?.map (·.plain)).getD 0 != 0 then
        [RoundSpec.silent "REPLY" (24 * (links.head?.map (·.plain)).getD 0) 0] else []) ++
      sendSeed y.set (sampledAt y l g links) roots ::
        locRound y.set .request before (24 * (y.set.samples * (sampledAt y l g links).length)) 0
          (y.set.samples * (sampledAt y l g links).length) :: rest := by
  have h0 : (l == 0) = false := by simpa using hl
  rw [reqListFrom]
  simp only [h0, Bool.false_eq_true, if_false, reqSendOpen, ht, Option.map_some, Option.getD_some,
    List.cons_append, List.nil_append]
  exact ⟨_, rfl⟩

/-! ### The two rounds, as the library's types have them -/

variable {E : Type} [Field E] [Fintype E] (z : Cb.Pv.SendLocRide.Size E)

/-- The plain parts: a single value in the first round; the answers of all members in the second. -/
theorem sendLoc_plains :
    (Cb.Pv.SendLocRide.R z).shape.map (·.Plain) = [Unit × Unit, z.sw.d.N.Answ × Unit] := rfl

/-- The oracle positions: the native positions of the rider's code and of all members' codes in the
first round; none in the second. -/
theorem sendLoc_places :
    (Cb.Pv.SendLocRide.R z).shape.map (·.Pos) =
      [z.Cw.NP ⊕ (Σ a, (z.sw.d.N.om a).C.NP), Empty ⊕ Empty] := rfl

/-- The verifier's messages: one seed for all members; then the positions. -/
theorem sendLoc_draws :
    (Cb.Pv.SendLocRide.R z).shape.map (·.Chal) = [z.sw.d.Sd.D, Fin z.sw.t → z.sw.P] := rfl

/-! ### The conditions -/

/-- The four conditions on the letters z of the block, at five numbers. -/
structure SendLocFits (samples cube answers t logN : ℕ) : Prop where
  /-- the seeds are, up to a bijection, samples * cube elements of E and samples elements of E that
  are not 0 -/
  seeds : Nonempty (z.sw.d.Sd.D ≃ DrawSet E (samples * cube) samples 0 0 0)
  /-- the rider's code or a member of the family has a native position -/
  place : Nonempty (z.Cw.NP ⊕ (Σ a, (z.sw.d.N.om a).C.NP))
  /-- the answers of all members together are, up to a bijection, `answers` elements of E -/
  answers : Nonempty (z.sw.d.N.Answ ≃ (Fin answers → E))
  /-- t positions are drawn, and the long positions of the open word's code are, up to a bijection,
  the numbers below 2 ^ logN -/
  positions : z.sw.t = t ∧ Nonempty (z.sw.P ≃ Fin (2 ^ logN))

/-- The largest number of variables of a sample's cube, in the words of sendSeed. -/
def largestCube (o : List SampleSize) : ℕ := o.foldl (fun c x => max c x.cubeBits) 0

/-! ### Three bijections -/

/-- A message of a single value: no element of E and none of F. -/
def noPlain (E F : Type) : Unit × Unit ≃ (Fin 0 → E) × (Fin 0 → F) where
  toFun := fun _ => (fun i => i.elim0, fun i => i.elim0)
  invFun := fun _ => ((), ())
  left_inv := fun _ => rfl
  right_inv := fun _ => Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0)

/-- The answers beside a single value: k elements of E and none of F. -/
def answersPlain {A : Type} (F : Type) {k : ℕ} (e : A ≃ (Fin k → E)) :
    A × Unit ≃ (Fin k → E) × (Fin 0 → F) where
  toFun := fun x => (e x.1, fun i => i.elim0)
  invFun := fun y => (e.symm y.1, ())
  left_inv := fun x => Prod.ext (e.symm_apply_apply x.1) rfl
  right_inv := fun y => Prod.ext (e.apply_symm_apply y.1) (funext fun i => i.elim0)

/-- t positions: a draw of t positions below 2 ^ logN and nothing else. -/
def positionsDraw {P : Type} (t logN : ℕ) (e : P ≃ Fin (2 ^ logN)) :
    (Fin t → P) ≃ DrawSet E 0 0 t logN 0 where
  toFun := fun f => (fun i => i.elim0, fun i => i.elim0, fun i => e (f i), fun i => i.elim0)
  invFun := fun y => fun i => e.symm (y.2.2.1 i)
  left_inv := fun f => funext fun i => e.symm_apply_apply (f i)
  right_inv := fun y => Prod.ext (funext fun i => i.elim0) (Prod.ext (funext fun i => i.elim0)
    (Prod.ext (funext fun i => e.apply_symm_apply (y.2.2.1 i)) (funext fun i => i.elim0)))

/-! ### The shape -/

/-- If there is a root, and under the four conditions at the numbers of the two descriptions, the
block's shape has the rounds of the entries of sendSeed s o roots and of the round of positions that
takes its answers in. -/
theorem sendLoc_shape (F : Type) (s : Setting) (c : Scope) (o : List SampleSize) (roots : ℕ)
    (g : GroupSize) (hr : roots ≠ 0)
    (h : SendLocFits z s.samples (largestCube o) (s.samples * o.length) (baseCount s c g)
      g.main.logN) :
    ShapeIsAll E F (Cb.Pv.SendLocRide.R z).shape
      [((sendSeed s o roots).round s c).entry,
        ((locRound s c g (24 * (s.samples * o.length)) 0 (s.samples * o.length)).round s
          c).entry] := by
  obtain ⟨⟨eS⟩, ⟨x⟩, ⟨eA⟩, ht, ⟨eP⟩⟩ := h
  refine List.Forall₂.cons ⟨⟨0, 0, ⟨noPlain E F⟩, ?_⟩, ?_, ⟨?_⟩, ?_⟩
    (List.Forall₂.cons ⟨⟨s.samples * o.length, 0, ⟨answersPlain F eA⟩, ?_⟩, ?_, ⟨?_⟩, ?_⟩
      List.Forall₂.nil)
  · show 32 * roots = 32 * roots + 24 * 0 + 8 * 0
    omega
  · show s.samples ≤ s.samples * (largestCube o + 1)
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  · show z.sw.d.Sd.D ≃ DrawSet E (s.samples * (largestCube o + 1) - s.samples) s.samples 0 0 0
    rw [Nat.mul_succ, Nat.add_sub_cancel]
    exact eS
  · exact ⟨fun e => (e.false x).elim, fun e => absurd e hr⟩
  · show 24 * (s.samples * o.length) = 32 * 0 + 24 * (s.samples * o.length) + 8 * 0
    omega
  · exact Nat.le_refl 0
  · show (Fin z.sw.t → z.sw.P) ≃ DrawSet E (0 - 0) 0 (baseCount s c g) g.main.logN 0
    rw [← ht]
    exact positionsDraw z.sw.t g.main.logN eP
  · exact ⟨fun _ => rfl, fun _ => inferInstanceAs (IsEmpty (Empty ⊕ Empty))⟩

/-- The same at the setting, the scope, the messages and the group at which reqList_sendLoc has the
two descriptions. -/
theorem sendLoc_listed (F : Type) (y : ProofSized) (l : ℕ) (g : ReqGroup) (links : List ReqLink)
    (before : GroupSize) (roots : ℕ) (hr : roots ≠ 0)
    (h : SendLocFits z y.set.samples (largestCube (sampledAt y l g links))
      (y.set.samples * (sampledAt y l g links).length) (baseCount y.set .request before)
      before.main.logN) :
    ShapeIsAll E F (Cb.Pv.SendLocRide.R z).shape
      [((sendSeed y.set (sampledAt y l g links) roots).round y.set .request).entry,
        ((locRound y.set .request before (24 * (y.set.samples * (sampledAt y l g links).length)) 0
          (y.set.samples * (sampledAt y l g links).length)).round y.set .request).entry] :=
  sendLoc_shape z F y.set .request (sampledAt y l g links) roots before hr h

end OnBytes.Tie.Pv.Switch
