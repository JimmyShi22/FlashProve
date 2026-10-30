-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamTuple.lean: **THE SEAM's CORE AS ONE COMPOSITION: FROM WHAT THE PROXIMITY TEST's GAME CONCLUDES (NTuple) TO ONE TUPLE OF TYPED MESSAGES, AT THE KIND's OWN RECORD.** One statement; its proof is calls of what lies in four groups of files. NO NEW
MATHEMATICS.
  tuple_core   at a record t of the kind, strings y, and whatever the record fixes (a · G0 · Ly · D): NTuple gives ∃ m (one typed message for each member of the rule of composition's list), with
               (i) every row that the test takes in says its claim of the words wordsT (Johnson/Desc/K14/Law/LedgerSay.lean) of m, at the statement behind the test's beginning · (ii) m is a candidate (CandAt) at every member of "mine".
THE ROAD: tupleAt_words (K12/Coin/TupleOfAt.lean: words_tuple · allSay_congr) · tuple_of_port (Sound/CandMove.lean: the cast, and the tuple) · words_member · run_agree (SeamWords.lean:
says_agree).
ITS PREMISES, EACH A PLAIN FACT, NONE WITH CHANCE IN IT:
  OF THE PLAN AND A YES: hJ (StageJ at the radius) · ht (combineAt behind the beginning) · hk | hh (the layout's k | h) · hS | hQ (siteL | sampleL say yes at every member) · **hfit (the radius against each member's: THE ONE COMPARISON OF NUMBERS)**
  OF THE RECORD: hI (the statement is in order) · hG (the group under test) · hmembers (the group's members are the data's) · hfind (the layout finds each member at its place) · seeds (each member's one sample row is Send.form's at a seed, with its answer; and
    the reading smp of the record gives a sample that the library's sample map reads alike: s2)
  OF THE LETTERS OF K12's FILES AND OF LedgerSay.lean: memJ (which member of the list sits at each of the data's) one to one · he (its entry is the member's shape with the radius e0s j) · hmem (the plan's mem lays it at the member's number) · s1 (the word off the plain strings is the word as
    sent) · hrd (the reader is tabP).
Limits. EVERY PREMISE IS A PREMISE. Called at no value. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamWords
import Johnson.Desc.Sound.CandMove
import Johnson.Desc.K12.Coin.TupleOfAt
import Johnson.Desc.K12.Law.BatValsPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok made_of oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

theorem tuple_core {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rdN : ℕ → ℕ) (t : T12) (y : Fr.E.Str) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.st.codes s.l).om i).Smp)
    (a0 : A) (Y : Strs) (mem : ℕ → Option Mem) (mine : List Mem)
    (rd : (x : Mem) → ((sigOf D.st.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP D.st.codes (x.1.l.get x.2).1 m part i)
    (hf : Fixes π t a rest G0 Ly D) (hN : NTuple Fr π no rad rdN (t, y) a rest G0 Ly D)
    (hJ : (sgOf a).StageJ (rad (sgOf a)))
    (ht : combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true)
    (hk : Ly.k = (sgOf a).h + (sgOf a).g) (hh : Ly.h = (sgOf a).h)
    (e0s : Fin D.mems.length → ℕ)
    (hS : ∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true)
    (hQ : ∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (hfit : ∀ j : Fin D.mems.length,
      rad (sgOf a) < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (hI : InOrder t.st)
    (memJ : Fin D.mems.length → Mem) (hinj : Function.Injective memJ)
    (hmine : ∀ x ∈ mine, ∃ j, memJ j = x)
    (he : ∀ j, (memJ j).1.l.get (memJ j).2 = ((D.mems.get j).sh, e0s j))
    (hmem : ∀ j, mem (D.mems.get j).id = some (memJ j))
    (hfind : ∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val)
    (hmembers : ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o)
    (seeds : ∀ j : Fin D.mems.length, ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row)
      (tt : E) (β : GEˣ), D.st.oracles[(D.mems.get j).id]? = some x ∧
      Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ∃ (z σ' : ((sigOf D.st.codes (memJ j).1.l).om (memJ j).2).Smp),
        smp a0 (memJ j).1 (memJ j).2 = some z ∧
        HEq (((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
          (portOmZ D.st.codes (D.mems.get j).sh (e0s j)).Smp) σ' ∧ z.2 = σ'.2 ∧
        ((sigOf D.st.codes (memJ j).1.l).om (memJ j).2).Z.val z.1 =
          ((sigOf D.st.codes (memJ j).1.l).om (memJ j).2).Z.val σ'.1)
    (s1 : ∀ j : Fin D.mems.length,
      HEq (strOf D.st.codes (D.mems.get j).sh (e0s j) (layOf (D.mems.get j))
          (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
        (VerifiableInference.Desc.Sound.wordsOf G D.st.codes (memJ j).1.l (memJ j).1.seat Y (memJ j).2)) :
    ∃ m : (x : Mem) → ((sigOf D.st.codes x.1.l).om x.2).Msg,
      AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
        (_root_.Desc.K14.Law.wordsT D.st.codes mem rd m) ∧
      ∀ x ∈ mine, CandAt D.st.codes G smp x a0 Y (m x) := by
  obtain ⟨row₀, hok, hT⟩ := hN
  obtain ⟨c', hall, hc⟩ := tupleAt_words (good_of_ok π a row₀ D hok)
    (made_of π _ a Ly D (hf.2.2.2 row₀)) t.st t.g G0 rdN _ _ _ (rad (sgOf a)) hJ ht hk hh e0s hS hQ
    hfit hT
  choose x seed row0 tt β hx hform hrows hzl hβ hs2 using seeds
  obtain ⟨m, hcand, hm⟩ := tuple_of_port D.st.codes G smp memJ hinj mine hmine
    (fun j => (D.mems.get j).sh) e0s he a0 Y _
    (fun j => ((readP (bitsZ D.st.codes (D.mems.get j).sh) (seed j).z, β j), fun _ => readE (tt j)))
    c' s1 hs2
    (fun j => hc j (x j) (hx j) (seed j) (row0 j) (tt j) (β j) (hform j) (hrows j) (hzl j) (hβ j))
  refine ⟨m, ?_, hcand⟩
  refine run_agree t.st _ hI (grows_begun _ _ _) t.g G0 hf.2.1 _ _ (fun o ho part i => ?_) hall
  obtain ⟨j, rfl⟩ := hmembers o ho
  exact words_member D c' mem rd hrd m j _ (hfind j) (memJ j) (hmem j)
    (congrArg Prod.fst (he j)) (hm j) part i

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tuple_core
