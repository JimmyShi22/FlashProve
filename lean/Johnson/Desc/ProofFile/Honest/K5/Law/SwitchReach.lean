-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SwitchReach.lean: THE SEAT OVER THE SWITCHES' SENDINGS
(`K2.switchSeat`, Johnson/Desc/ProofFile/Honest/K2/OwnData.lean) REACHES EVERY MESSAGE OF MOMENT 0
OF THE SEGMENTS 1 TO 23. On public data alone. CONDITIONAL: in the goals' scope; at an opening of
the description's maker's return, at the maker's own ground; where the description passes its own
test on the plan. Five theorems.

What it is for. The premise's form `LaysFilling` (LaysFilling.lean in this folder) has a public
field, reach: each array that the values have lies in a message that is seated at an address. This
file pays the half of it that does not speak of arrays, at the seat that lies typed over the
switches' sendings.

Main names:
  `switchSeat_reaches`: **the sentence above**: there is an address at which the seat answers (l,
    m).
  `switch_into`: a place of `K2.switchPlaces Z Bs.G₀` stands at (chain 1, segment l, piece 1, the
    code switch's kind) and leads into segment l.
  `k2_spot_at_link`: the plan's list has a place of the kind there. No test on the plan is asked.
  `switch_of_spot`: a place of the kind in the plan's list is a place of `K2.switchPlaces Z G`, WITH
    THE SEGMENT INTO WHICH IT LEADS. `ownSeats_apart`: at an opening the addresses of `K2.ownSeats Z
    G` are pairwise apart, at every ground.

How. `seatBy_at`, `msgNo_of_moment` (SeatReach.lean in this folder); `k2_places_sub`,
`k2_place_there` (Johnson/Desc/ProofFile/Honest/Thread/SwitchPlaces.lean); `H2K12.places_apart`,
`table_apart`, `table_is`, `entry_own` (Johnson/Loose/H2K12/SpotsAtAll.lean); `IM.Open.first`
(Johnson/IMR/SeatOpen.lean). `k2_spot_at_link` GOES THE WAY OF `IM.k2_link_of`
(Johnson/IMR/K2Seat.lean), by the same calls (`IM.chain_hear_first`, `IM.lot_K2`, `IM.subs_at`,
`IM.subs_att`): that theorem's proof knows the entry's place as an equation and its statement does
not hand it out. `switch_of_spot` has the text of `k2_place_of_spot` (SwitchPlaces.lean) with one
conjunct more.

Limits. The segments 1 to 23: not segment 0, whose first sending stands at a place of another kind;
not the head's segment. Moment 0 alone. Which address it is is not stated. That the seat undoes the
places' own addresses (`K2.SwitchPlace.ownAddr`) is not stated. Of what a message holds nothing is
said. Through its imports the file stands above Cb/Bridge/CodeListRSProved.lean, and so above the
files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function, but for `ownSeats_apart` and `switch_of_spot`.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReach
import Johnson.Desc.ProofFile.Honest.Thread.SwitchPlaces
import Johnson.IMR.K2Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)

/-- **A place of the kind in the plan's list is a place of the switches' list, with the segment into
which it leads.** Conditional: hP, hs: what the kind makes once of the plan, and the plan's list,
are made; hsp, hk: sp is a place of the kind in that list. -/
theorem switch_of_spot {Z : Pub} {G : Ground} {P : P1K2.Prep} {sps : List Spot}
    (hP : P1K2.prepOf Z G = some P) (hs : spotsOf Z.cuts = some sps) {sp : Spot} (hsp : sp ∈ sps)
    (hk : sp.place.kind = .K2) :
    ∃ p ∈ K2.switchPlaces Z G, p.place = sp.place ∧
      p.link = sp.place.link.getD P.z.request.link.length := by
  unfold K2.switchPlaces
  rw [hP, hs]
  exact ⟨_, List.mem_map.2 ⟨sp, List.mem_filter.2 ⟨hsp, by rw [hk]; rfl⟩, rfl⟩, rfl, rfl⟩

section
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- **The addresses of the switches' own messages' seats are pairwise apart.** CONDITIONAL: an
opening of the description's maker's return. At every ground. -/
theorem ownSeats_apart (O : IM.Open o pol lay KL F Z Bs base c A B) (G : Ground) :
    (K2.ownSeats Z G).Pairwise fun x y => x.1 ≠ y.1 := by
  have hN : ((K2.switchPlaces Z G).map (·.place)).Nodup :=
    (SwitchPlaces.k2_places_sub Z G).nodup (H2K12.places_apart (H2K12.table_apart O).1)
  unfold K2.ownSeats
  rw [List.pairwise_map]
  exact (List.pairwise_map.1 hN).imp fun hab e => hab (congrArg Addr.place e)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The plan's list has a place of the kind at the first piece of each segment from 1 to 23.**
CONDITIONAL: the two premises on the public files; an opening; l is from 1 to 23. -/
theorem k2_spot_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h1 : 1 ≤ l)
    (h24 : l < 24) : ∃ sp ∈ P1K2.purePlaces Z, sp.place = ⟨1, some l, 1, .K2⟩ := by
  have hl0 : (l == 0) = false := by simpa using (by omega : l ≠ 0)
  have key : ∀ sub : ModelPart, sub ≠ .head → (subsOf Z)[l]? = some sub →
      ∃ x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀, x.place = ⟨1, some l, 1, .K2⟩ := by
    intro sub hsub hs
    have hk : (kindsBeforeBatching sub (l == 0))[0]? = some KindName.K2 := by
      rw [hl0]
      cases sub
      · rfl
      · rfl
      · exact absurd rfl hsub
    obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hla⟩ :=
      IM.chain_hear_first O.made O.places O.chain l sub hs 0 .K2 hk (by decide)
    obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [ep])
    exact ⟨x, hx, ep⟩
  have hx' : ∃ x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀,
      x.place = ⟨1, some l, 1, .K2⟩ := by
    by_cases he : l % 2 = 0
    · have h := IM.subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at h
      exact key .layers (by decide) h
    · have h := IM.subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at h
      exact key .attention (by decide) h
  obtain ⟨x, hx, epx⟩ := hx'
  have hN := (H2K12.table_apart O).1
  rw [H2K12.table_is] at hx
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hx
  exact ⟨sp, hsp, (H2K12.entry_own hN sp hsp).symm.trans epx⟩

/-- **A SWITCH LEADS INTO EACH SEGMENT FROM 1 TO 23.** CONDITIONAL: as above; hF: the description
passes its own test on the plan. -/
theorem switch_into (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true) {l : ℕ}
    (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ p ∈ K2.switchPlaces Z Bs.G₀, p.place = ⟨1, some l, 1, .K2⟩ ∧ p.link = l := by
  obtain ⟨p₀, hp₀, -⟩ := SwitchPlaces.k2_place_there Z O hF
  obtain ⟨sp, hsp, esp⟩ := k2_spot_at_link hS hR O h1 h24
  unfold K2.switchPlaces at hp₀
  split at hp₀
  · rename_i Pq sps hP hs
    unfold P1K2.purePlaces at hsp
    rw [hs] at hsp
    obtain ⟨p, hp, e1, e2⟩ := switch_of_spot hP hs (List.mem_filter.1 hsp).1 (by rw [esp])
    exact ⟨p, hp, e1.trans esp, by rw [e2, esp]; rfl⟩
  · cases hp₀

/-- **THE SEAT REACHES EVERY MESSAGE OF MOMENT 0 OF THE SEGMENTS 1 TO 23.** CONDITIONAL: as above;
hM, h0: M is message number m of segment l of the public part's shape, of moment 0. -/
theorem switchSeat_reaches (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true) {l : ℕ}
    (h1 : 1 ≤ l) (h24 : l < 24) {m : ℕ} {M : OnBytes.Params.ReqMessage}
    (hM : (Z.first.shape.link.getD l default).messages[m]? = some M) (h0 : M.moment = 0) :
    ∃ Ad : MsgAddr, K2.switchSeat Z Bs.G₀ Ad = some (l, m) := by
  obtain ⟨p, hp, -, e2⟩ := switch_into hS hR O hF h1 h24
  obtain ⟨k, hk⟩ := msgNo_of_moment hM
  rw [h0] at hk
  have hx : ((⟨p.place, 0⟩ : Addr), l, 1 + p.sizes.kept.length) ∈ K2.ownSeats Z Bs.G₀ := by
    unfold K2.ownSeats
    exact List.mem_map.2 ⟨p, hp, by rw [e2]⟩
  refine ⟨⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + k⟩, ?_⟩
  unfold K2.switchSeat
  rw [IM.Open.first O]
  exact seatBy_at (ownSeats_apart O Bs.G₀) hx hk

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.switch_of_spot
#print axioms ProofFile.Honest.K5.ownSeats_apart
#print axioms ProofFile.Honest.K5.k2_spot_at_link
#print axioms ProofFile.Honest.K5.switch_into
#print axioms ProofFile.Honest.K5.switchSeat_reaches
