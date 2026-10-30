-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeySealTie.lean: FROM «NO CLASH AT THE SEED» IN A LIBRARY's LIST TO NoColl (Johnson/Desc/Msg.lean) OF A TABLE's READING: THE BARE STEP, general: beneath it stand Johnson/Desc/Msg.lean and Cb/Gen/OodDec.lean alone: no kind's files.
  noColl_of_noClash   where every member of the table's list (near the committed word; meets the sample in the record) is carried into the library's list by a map that is injective ON THE MEMBERS (M may be one type for all messages: a table with an entry outside its shape must then be no member) and has ONE answer there at the seed ρ: no clash at ρ
                      gives NoColl. THE TABLE THAT toU READS IS THE TABLE AS LAID (what msgOf gives: the message with its pad's places): two tables that part at a pad's place alone must have two images
  SealReads           (T1) WHAT A SEAT ASKS OF THE READING G, AS ONE NAMED PROPERTY, AT LETTERS: Lst (the library's list of the word that is read off the oracles) · ev (its sample map) · seedIs («the record's sample rows of the message are the kind's one row at
                      the seed ρ, with the answer y») · str (the oracles as Msg.lean's Strs): has: where seedIs holds the record holds a sample · toU · inj (on the members) · mem
  sealed_gives        (T2) THE BRIDGE «S»: SealReads → (∃ ρ y, seedIs a ρ y ∧ no clash at ρ) → hasSmp ∧ NoColl. AT THE CALL: Lst y := (portOmZ cs s e).InList (fOf y) · ev := (portOmZ cs s e).Z.val · seedIs: SEE sealed_gives_lift: the library's sample map answers in Z.S → GE, the kind's
                      SeedIs in GE
  sealed_gives_lift   THE ADAPTOR FOR THE CALL: seedIs₀ a := SeedIs cs s (stOf a) (oOf a) · lift y := fun _ => y: the premise is then MEANT to be the sending kind's «Sealed cs s e (fOf y) (stOf a) (oOf a)», unfolded: BY READING: NOT
                      HELD BY LEAN HERE (Johnson/Desc/K1/Law/SeedIs.lean | GoodSend3.lean do not lie beneath this file); the sending kind's files' own sealed_noClash (K1/Law/SealTie.lean: not in this library) states that unfolding
WHAT IT ASKS OF THE READING G (hmem): THE TABLE's LIST LIES INSIDE THE LIBRARY's, AND «meets the sample in the record» MEANS «has the library's answer at the seed». It is the specification of G's letters enc · rad · meets · smp at a tenant.
EMPTY WHERE: the record holds no sample (NoColl is free there: the promise asks hasSmp beside it). Nothing on soundness by itself.
-/
import Johnson.Desc.Msg
import Cb.Gen.OodDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open VerifiableInference.Desc

section
variable {Xi A Cells M Smp Rec : Type} (F : FileDescription Xi) (G : Reading A Cells M Smp Rec)

/-- **The bare step.** -/
theorem noColl_of_noClash {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ : D) (ans : Y) (j t : Nat) (a : A) (y : Strs) (toU : M → U)
    (hinj : ∀ o z m m', F.oracleAt j = some o → G.smp a j t = some z → Member F G o j t y z m → Member F G o j t y z m' → toU m = toU m' → m = m')
    (hmem : ∀ o z m, F.oracleAt j = some o → G.smp a j t = some z → Member F G o j t y z m → Lst (toU m) ∧ ev ρ (toU m) = ans)
    (hno : ¬ Cb.Ood.Clash Lst ev ρ) : NoColl F G j t a y := by
  intro o z ho hz m m' hm hm'
  obtain ⟨h1, h2⟩ := hmem o z m ho hz hm
  obtain ⟨h1', h2'⟩ := hmem o z m' ho hz hm'
  by_contra hne
  exact hno ⟨toU m, toU m', h1, h1', fun e => hne (hinj o z m m' ho hz hm hm' e), h2.trans h2'.symm⟩

/-- **(T1) What a seat asks of the reading.** Y': the oracles' type at the rule's statement; str: read as Msg.lean's plain functions. -/
structure SealReads {U D Y Y' : Type} (str : Y' → Strs) (Lst : Y' → U → Prop) (ev : D → U → Y) (seedIs : A → D → Y → Prop) (j t : Nat) where
  /-- the table as laid (the message with its pad's places), as a message of the library's -/
  toU : M → U
  /-- where the record's rows are the kind's, the reading returns a sample -/
  has : ∀ a ρ y, seedIs a ρ y → hasSmp G j t a = true
  /-- two members with one image are one -/
  inj : ∀ (a : A) (y' : Y') o z m m', F.oracleAt j = some o → G.smp a j t = some z → Member F G o j t (str y') z m → Member F G o j t (str y') z m' → toU m = toU m' → m = m'
  /-- the table's list lies inside the library's, and «meets the sample in the record» means «has the library's answer at the seed» -/
  mem : ∀ (a : A) (y' : Y') o z m ρ y, F.oracleAt j = some o → G.smp a j t = some z → seedIs a ρ y → Member F G o j t (str y') z m → Lst y' (toU m) ∧ ev ρ (toU m) = y

/-- **(T2) The bridge «S»: sealed gives the promise's two parts at the new pin.** -/
theorem sealed_gives {U D Y Y' : Type} (str : Y' → Strs) (Lst : Y' → U → Prop) (ev : D → U → Y) (seedIs : A → D → Y → Prop) (j t : Nat)
    (H : SealReads F G str Lst ev seedIs j t) (a : A) (y' : Y') (h : ∃ ρ y, seedIs a ρ y ∧ ¬ Cb.Ood.Clash (Lst y') ev ρ) :
    hasSmp G j t a = true ∧ NoColl F G j t a (str y') := by
  obtain ⟨ρ, y, hs, hno⟩ := h
  exact ⟨H.has a ρ y hs, noColl_of_noClash F G (Lst y') ev ρ y j t a (str y') H.toU (fun o z m m' => H.inj a y' o z m m')
    (fun o z m ho hz hm => H.mem a y' o z m ρ y ho hz hs hm) hno⟩

/-- **The adaptor for the call** (the library's sample map answers in Z.S → GE, the sending kind's SeedIs in GE): the record's answer y₀ is lifted. At the call: Y₀ := GE · lift y := fun _ => y: the premise h is then meant to be
the sending kind's «Sealed» (Johnson/Desc/K1/Law/GoodSend3.lean), unfolded: by reading, not by a build. -/
theorem sealed_gives_lift {U D Y Y₀ Y' : Type} (str : Y' → Strs) (Lst : Y' → U → Prop) (ev : D → U → Y) (lift : Y₀ → Y) (seedIs₀ : A → D → Y₀ → Prop) (j t : Nat)
    (H : SealReads F G str Lst ev (fun a ρ v => ∃ y₀, seedIs₀ a ρ y₀ ∧ v = lift y₀) j t) (a : A) (y' : Y')
    (h : ∃ ρ y₀, seedIs₀ a ρ y₀ ∧ ¬ Cb.Ood.Clash (Lst y') ev ρ) : hasSmp G j t a = true ∧ NoColl F G j t a (str y') := by
  obtain ⟨ρ, y₀, hs, hno⟩ := h
  exact sealed_gives F G str Lst ev _ j t H a y' ⟨ρ, lift y₀, ⟨y₀, hs, rfl⟩, hno⟩

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.sealed_gives_lift
#print axioms VerifiableInference.Desc.Key.sealed_gives
#print axioms VerifiableInference.Desc.Key.noColl_of_noClash
