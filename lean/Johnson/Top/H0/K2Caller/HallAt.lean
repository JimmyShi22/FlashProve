-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/HallAt.lean: the code switch: WHAT THE JOIN FOR THE KEPT MEMBERS' PINS
(`pinJT_kept`, PinKeptJoin.lean) ASKS OF EVERY MEMBER OF THE TABLE's LIST AT A KEPT TENANT, in one
theorem.

Main names:
  `hall_at`: from: the law's own condition in front (`keptFacts_at`, KeptFactsAt.lean) · the table
    of joints' side (`tableSide_of`, `one_number_of`: TableSide.lean): one test on the plan
    (`keptSeatsB`), three tests on the verifier's state's book, that the book has a place for each
    kept old message, that the file's columns are read by the tree's number, that every leaf is
    shown, that both copies have one number · hAl: each member of the table's list at that tenant is
    one whose pad the row lays, and is alike a typed kept member.
Limits. Every one of these is a premise here; who pays which stands in a page that is not in this library.
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.KeptFactsAt
import Johnson.Top.H0.K2Caller.TableSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (SeatFits ShownAt Mem SitsAt shownJT numAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (keptBitsB keptShapeB storedB hx_of)

variable {r : SwRow} {H : r.OK} {Xi P : Type} (G : FileDescription Xi)
  (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2)
  (orc : Strs → ℕ → ℕ → List UInt64) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ)) (L : Laid)
  (trees : ℕ)

/-- **WHAT THE JOIN FOR THE KEPT MEMBERS' PINS ASKS OF EVERY MEMBER AT A KEPT TENANT**
    (`pinJT_kept`'s
premise on all members, PinKeptJoin.lean), from: the law's own condition in front (`keptFacts_at`) ·
the table of joints' side (`tableSide_of`, `one_number_of`: TableSide.lean) · hAl: each member of
the table's list at that tenant is one whose pad the row lays, and is alike a typed kept member. -/
theorem hall_at (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (P12 : Pub12 (r := r) W₀ fx)
    (hchk : switchTargetCheck (K2.skelOf fx) fx.f.rows fx.T = true) (hG : K2.SampleGoodS fx.st)
    (hk : r.keptAt W₀ = true) (hb : keptBitsB r W₀ = true) (hs : keptShapeB r = true)
    (hS : storedB r W₀ fx = true)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ (memK (r := r) (H := H)) rowK (plK W₀))
    (hst : a.2.st.oracles = fx.st.oracles) (hSF : ∀ k : {a // (plainHd r H).cl a}, SeatFitAt G r.cs
        r.lo seat k.1.1) (olds : List ℕ)
    (hB : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true)
    (ho : ∀ k : {a // (plainHd r H).cl a},
      olds[r.kept.idxOf k.1.1.val]? = some (keptK2 r H W₀ k).old)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (hold : ∀ k : {a // (plainHd r H).cl a}, (keptK2 r H W₀ k).old < t.book.place.size)
    (horc : ∀ j, j < trees → ∀ x, orc y j x = y.col j x) (news : List (ℕ × ℕ))
    (hal : ∀ k : {a // (plainHd r H).cl a}, ∃ w, news[1 + r.kept.idxOf k.1.1.val]? = some w ∧
      arr (seat k.1.1).1 (seat k.1.1).2 = arr w.1 w.2)
    (hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩))
    (ms minePad : List Mem) (q : ℕ × ℕ) (hsh : shownJT r.cs G ms q.1 q.2 y)
    (hAl : ∀ x ∈ ms, SitsAt x q.1 q.2 → x ∈ minePad ∧
      ∃ k : {a // (plainHd r H).cl a}, VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩)
          :
    ∀ x ∈ ms, SitsAt x q.1 q.2 → x ∈ minePad ∧
      ∃ (k : {a // (plainHd r H).cl a}) (kk : KeptPlace) (xo : OnBytes.Oracle),
        VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩ ∧
          KeptFacts G seat seatN p orc arr seats a t fx W₀ y k kk xo := by
  intro x hx hq
  obtain ⟨hp, k, hA⟩ := hAl x hx hq
  obtain ⟨xo, hmsg, hshp, -⟩ := hx_of hk hS ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩
  obtain ⟨s1, s2, s3, s4⟩ := tableSide_of G seat p orc seats L trees t fx W₀ y k (hSF k) olds hB (ho
      k)
    hIn hSe hFi q₀ h0 (hold k) xo hmsg hshp horc ms q hsh x hx hq hA
  obtain ⟨xo', KF⟩ := keptFacts_at G seat seatN p orc arr seats a t fx W₀ y P12 hchk hG hk hb hs hS
    Ft hst k s1 s2 s3
    (one_number_of seat news arr seatN (r.kept.idxOf k.1.1.val) k.1.1 (hal k) (hN _)) s4
  exact ⟨hp, k, _, xo', hA, KF⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hall_at
