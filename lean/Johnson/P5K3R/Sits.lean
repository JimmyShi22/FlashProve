-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/Sits.lean: the row K03_sits of the list of owed laws (in a file that is not in this
library), at the proof file: one theorem, a joining of other files' lemmas.

What the row asks: in the written description that seats the kind "lookup", the entry of the
description's list of blocks at each place of the kind is the constant of which the kind's laws
speak, at the plan's numbers, under the seat's wrappers alone (another name and place; the mark's
guard).

Main names:
  `k03_sits`: where the proof file's written description returns F, for public files in scope: F is
    made of a first chain c, and for every link l below 25 and both lookups: the entry of c's flat
    list at the number 14 l + i + 2 (i the lookup's number among the link's hearing blocks) is a
    block b such that: the kind's own text `K3.theStated`, at the lot's letters, the public record X
    and the driver's address, returns a block b'; b is b' under the seat's wrappers alone
    (`IM.LaidAlone`: THREE wrappers: another name and place; the mark's guard; the guard on the
    reply's seat, which also stands around every run of claims); b narrows b' (the same rounds; a
    yes of b is a yes of b' at the same records); a yes of b leaves no mark.
  `k03_yes`: a yes of the seated block is a yes of the kind's own block, with no mark behind it and
    the reply as it was, and the other way round.

Whose lemmas: that the entry of the link's hearing list is the lot's block under the wrappers
(`IM.k3_of`), that this entry stands in the flat list at that number (`IM.hear_at_flat`,
`IM.flatIx_scope`), what the wrappers leave of a yes (`IM.alone_underR`, `IM.yes_alone`), and the
walk through the maker (`IM.seat_open`) are those of the files of Johnson/IMR/. Here they are
called, and laid together with `Block.Narrows`, in which the laws of the kind are stated.

Limits: the row's own words name two wrappers; here there are three (above): the row's second arm
("or its yes gives that law's premise") is what `Narrows` says. Fifty entries are named; that no
other entry of the three flat lists bears the kind is not said. That the written description returns
in scope is a premise; the small stored set is outside that scope. Nothing on which string the
seated block's name is, on the link's order, its tests or its batching. Nothing on the pieces of the
rule for a file (a block below a lift): the tie to these is another file's. The key file's places of
the kind are another row. Nothing on soundness; nothing on hiding.


-/
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.Sound.SeatNarrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **K03_sits, at the proof file.** -/
theorem k03_sits {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      publicOf P.pol P.KL (some lay) = .ok X ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ l < 25, ∀ digits : Bool, ∃ b b' : Block S Cl,
        c.blocksInOrder[14 * l + IM.k3Ix l digits + 2]? = some b ∧
        VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt X) X Z.first.codes
          Z.first.shape (IM.k3Place l digits) = some b' ∧
        IM.LaidAlone ProofFile.sameReply b b' b.name (IM.k3Place l digits) ∧
        b.Narrows b' ∧
        ∀ s rs gs t, b.decide s rs gs = .ok t → t.failed = none := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Bs.G₀.W, Z, c, A, B, O.pub, O.public, O.desc, ?_⟩
  intro l hl digits
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl digits
  have h5 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l digits)] at h5
  refine ⟨b, b', h5, h3, h4, IM.alone_underR h4, ?_⟩
  intro s rs gs t hy
  exact ((IM.k3_yes h4 s t rs gs).1 hy).2.1

/-- A yes of the seated block, both ways. -/
theorem k03_yes {b b' : Block S Cl} {l : ℕ} {digits : Bool}
    (h : IM.LaidAlone ProofFile.sameReply b b' b.name (IM.k3Place l digits)) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  IM.k3_yes h s t rs gs

end K3Lot
