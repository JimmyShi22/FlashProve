-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeldNamesAt.lean: code switching: Held (K2Hands/Numbering.lean: what is asked
of the held messages' names), AT THE LAW's OWN TWO LETTERS aOf := Johnson.G.aOfK r H (a held
message's place in r.kept) and iOf := fun _ _ => 0 (K2Caller/PlaceLaw.lean has these two), AT AN
ACCEPTANCE. typed_of_yes (K2Caller/TypedAtT3.lean), which concludes T3At.typed's first and third
clauses, takes Held as a premise.
Theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  held_of_one    Held St W₀ … from r.keptAt W₀ and: at each kept member's entry of W₀ the statement
                 St stores JUST ONE OOD answers' row
  one_at_yes     that count at the statement S3 of an acceptance is the count at the front's
                 statement (old_at_yes, K2Hands/TiePaid.lean), where the entry's old number is below
                 the front's count of oracle messages
  held_of_yes    so Held S3 W₀ … at an acceptance, from r.keptAt W₀, FrontLight and: at each entry
                 of W₀.kept the front's statement stores just one row (the premise hone of
                 rows_debts, Tw/K2C/RowsDebts.lean, to the letter)
LIMITS. r.keptAt W₀ (a test on the main rows by place alone), FrontLight and hone stay premises.
T3At.typed binds no aOf | iOf: that these are the law's own two letters buys nothing at that
spender. Shown at no real state. No soundness is claimed. On hiding nothing.
-/
import Johnson.G.SwitchSampleTop
import Johnson.Top.H0.Tw.K2C.OnlyAtLight
import Johnson.Top.H0.K2Caller.TopAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (aOfK numAt numAt_inj k₀Plain hmem_of kept_len)

/-- **Held, where each kept member's entry has just one stored row.** -/
theorem held_of_one {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {W₀ : SwitchFrame} {St : Statement} (hk : r.keptAt W₀ = true)
    (h1 : ∀ k ∈ W₀.kept, (samplesOf St k).length = 1) :
    Held (Kh := (selLoc (Letters.plain r H) iJ iQ).hd.K)
      (Sk := fun k => ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S) St W₀ (aOfK r H)
      (fun _ _ => 0) where
  member := fun k => ⟨_, hmem_of hk ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩, fun _ => by
    rw [h1 _ (List.mem_of_getElem? (hmem_of hk ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩))]
    exact Nat.one_pos⟩
  twoK := fun k k' e => by
    have e1 := numAt_inj r ⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ ⟨⟨k'.1.1, k'.2.fst⟩, k'.2.snd⟩ e
    have e2 : k.1.1 = k'.1.1 := congrArg (fun a : {a // r.kp a} => a.1.1) e1
    exact Subtype.ext (Subtype.ext e2)
  twoS := fun _ _ _ _ => rfl
  all := fun a p i hp hi => by
    have ha : a < r.kept.length := by
      rw [← kept_len hk]
      exact (List.getElem?_eq_some_iff.1 hp).1
    have hj : r.kept[a] ∈ r.kept := List.getElem_mem ha
    have hlt : r.kept[a] < r.lo.length := H.kept_lt hj
    have hm : r.mem ⟨r.kept[a], hlt⟩ := by
      have h := H.kept _ hj
      rw [List.getElem?_eq_getElem hlt] at h
      simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    refine ⟨⟨⟨⟨r.kept[a], hlt⟩, ?_⟩, ?_⟩, (), List.Nodup.idxOf_getElem H.nodup a ha, ?_⟩
    · exact hj
    · exact ⟨hm, hj⟩
    rw [h1 p (List.mem_of_getElem? hp)] at hi
    omega

/-- The stored rows of an old message at the statement of an acceptance are the front's. -/
theorem one_at_yes {p : K2.P2} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c) (k : KeptPlace)
    (ho : k.old < fx.st.oracles.size) : samplesOf S3 k = samplesOf fx.st k := by
  unfold samplesOf
  rw [(old_at_yes Y1 k.old ho).2]

/-- **Held at an acceptance.** -/
theorem held_of_yes {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {W₀ : SwitchFrame} {p : K2.P2} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c) (hk : r.keptAt W₀ = true)
    (P : FrontLight r.cs r.l W₀ fx)
    (hone : ∀ k ∈ W₀.kept, (fx.st.oracles.getD k.old default).sampleRows.size = 1) :
    Held (Kh := (selLoc (Letters.plain r H) iJ iQ).hd.K)
      (Sk := fun k => ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S) S3 W₀ (aOfK r H)
      (fun _ _ => 0) := by
  refine held_of_one H iJ iQ hk fun k hkm => ?_
  obtain ⟨W, carried, L⟩ := laid_of Y1.made
  have eW : W₀ = W := by
    have h1 := L.frame
    rw [K2.frame_of_front Y1, P.frameIs] at h1
    exact Option.some.inj h1
  subst eW
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hkm
  obtain ⟨hi, e, -⟩ := kept_rec S3 fx.f.rows fx.T _ _ W₀ L.frame a k ha
  have ho : k.old < fx.st.oracles.size := by
    rw [e]
    exact K2.keptOld_of Y1.check P.keptPos _ (Array.getElem_mem_toList hi)
  rw [one_at_yes Y1 k ho]
  unfold samplesOf
  rw [Array.length_toList]
  exact hone k hkm

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.held_of_one
#print axioms VerifiableInference.Desc.First.K2Caller.one_at_yes
#print axioms VerifiableInference.Desc.First.K2Caller.held_of_yes
