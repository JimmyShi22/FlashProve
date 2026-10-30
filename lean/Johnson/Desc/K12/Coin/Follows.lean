-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Follows.lean: THE SECOND SENTENCE OF THE KIND's LAW, OF A STAGE's OWN VIEW:
what `Block.step` deals to the proximity test's stages out of `sView` FOLLOWS the written columns
(`Follows … (srcFirst …)`, Johnson/Desc/K12/Law/Written.lean). Statements and proofs.

  `laid_stored`: no declared round of a place opens a stored table.
  `flat_laid`: the declared openings of all the rounds are "BAT"'s and then those behind it.
  `follows_of_yes`: under `wants` (the stage's wants are the declared rounds' wants, each tree by
    its number over the file), the first two lines of `Block.step`, no column left over, `dealOk`,
    the first switch's openings against the letter gT (`hfirst`) and `OwnCols`.
By `dealt_by_src` (ViewSrc.lean), `dealt_wide` (Kpw.lean), `srcFirst_src` (Src.lean).
A tool.
-/
import Johnson.Desc.K12.Coin.Yes
import Johnson.Desc.K12.Coin.ViewSrc
import Johnson.Desc.K12.Coin.Kpw
import Johnson.Desc.Sound.TilesCutProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Sw
open H2K.First (dealOk dealt_of_ok nOpen_of_flat ownN)

theorem laid_stored (π : P12) : ∀ d ∈ (laidOf π).map (·.1), d.stored = [] := by
  intro d hd
  unfold laidOf at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  cases hrn : H2U.roundsOfNums π.nums with
  | none =>
    rw [hrn] at hx
    simp at hx
  | some rds =>
    rw [hrn] at hx
    exact roundsOfNums_stored _ rds hrn _ (List.of_mem_zip hx).1

theorem flat_laid (π : P12) : ((laidOf π).map (·.1)).flatMap (·.opens) =
    (((laidOf π).take 1).map (·.1)).flatMap (·.opens) ++
      ((laidS π).map (·.1)).flatMap (·.opens) := by
  unfold laidS
  rw [← List.flatMap_append, ← List.map_append, List.take_append_drop]

theorem follows_of_yes (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (ds : List RDT)
    (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (hdeal : dealOk π = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: rest) {s : Sg}
    (ch : OnBytes.Slice.Chain s) (hst : stagesOf ch = π.nums.stages) (y : F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) ds))
    (hw : ∀ Rs, wantsOf F.a (⟨F.a, base, F.all, ds, F.key, F.all⟩ : StageD).depth ds Rs =
      wantsDecl num (proximityTestKind guardedProximityTestParts π : Blk').rounds Rs)
    (hfit : roundsFit (proximityTestKind guardedProximityTestParts π : Blk').rounds (rvT (ckP .two) ds τ) = true)
    (hcols : (((sView (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ).opened.take
        ((groupsOf F.ft (proximityTestKind guardedProximityTestParts π : Blk').rounds
          ((rvT (ckP .two) ds τ).map (·.drawn))).flatMap id).length).map
        (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F.ft (proximityTestKind guardedProximityTestParts π : Blk').rounds
        ((rvT (ckP .two) ds τ).map (·.drawn))).flatMap id) = true)
    (hdrop : (sView (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ).opened.drop
      ((groupsOf F.ft (proximityTestKind guardedProximityTestParts π : Blk').rounds
        ((rvT (ckP .two) ds τ).map (·.drawn))).flatMap id).length = [])
    (ts : List ℕ) (gT : ℕ → ℕ → List UInt64)
    (hfirst : ∀ (i : ℕ) (o : ToldO) (x : ℕ) (col : List UInt64),
      ((cutS (laidS π) a.k).flatMap (·.opens))[i]? = some o →
      PCol (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ num o x col →
      col = gT (ts.getD i 0) x)
    (b : ch.Bl)
    (hO : OwnCols (PCol (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ num)
      (π.nums.free + (ownN π + 0)) ch b) :
    Follows (grpsS π (regroup ((groupsOf F.ft (proximityTestKind guardedProximityTestParts π : Blk').rounds
        ((rvT (ckP .two) ds τ).map (·.drawn))).map (·.length))
      ((sView (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ).opened.take
        ((groupsOf F.ft (proximityTestKind guardedProximityTestParts π : Blk').rounds
          ((rvT (ckP .two) ds τ).map (·.drawn))).flatMap id).length)))
      (srcFirst ch b (laidS π) ts gT) := by
  intro i grp hi z hz
  have hR := H2K.Sw.k12_rounds guardedProximityTestParts π hp
  have hd : ∀ d ∈ (proximityTestKind guardedProximityTestParts π : Blk').rounds, d.stored = [] := by
    rw [hR]
    exact laid_stored π
  have hlen : (proximityTestKind guardedProximityTestParts π : Blk').rounds.length =
      (drawnT (ckP .two) ds (rhoT (ckP .two) ds τ)).length := by
    rw [← rvT_drawn, List.length_map]
    exact roundsFit_length _ _ hfit
  have hcols' := beq_iff_eq.1 hcols
  unfold grpsS at hi
  rw [List.getElem?_drop] at hi
  obtain ⟨o', ho', Hw⟩ := dealt_wide F.ft _ hd _ _ hcols' _ grp hi
  rw [List.take_of_length_le (List.drop_eq_nil_iff.1 hdrop), rvT_drawn] at hi
  obtain ⟨o, ho, Hc⟩ := dealt_by_src (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ num F.ft
    _ hd hlen (hw _) (sCol_isSome (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ _) _ grp hi
  obtain rfl := Option.some.inj (ho'.symm.trans ho)
  have hn0 : nOpen (((laidOf π).take 1).map (·.1)) =
      ((((laidOf π).take 1).map (·.1)).flatMap (·.opens)).length :=
    nOpen_of_flat _ fun d hd' => laid_stored π d (by
      rw [List.map_take] at hd'
      exact List.mem_of_mem_take hd')
  rw [hR, flat_laid, hn0, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left] at ho
  exact srcFirst_src π _ ch a rest (laidS π) (hst.trans hs) (dealt_of_ok π a rest hs hdeal) ts gT
    hfirst b hO (fun d hd' => laid_stored π d (by
      unfold laidS at hd'
      rw [List.map_drop] at hd'
      exact List.mem_of_mem_drop hd')) i o' ho z.1 z.2 ⟨Hc z hz, (Hw z hz).1, (Hw z hz).2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.follows_of_yes
