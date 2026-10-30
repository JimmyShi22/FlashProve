# The outcome of the full check

Terms: [TERMS.md](TERMS.md).

One Lean file, `AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean`, was added after the runs reported on this page. It contains one definition, `VerifiableInference.executableVerifier`, and four theorems (`executableVerifier_eq_leanVerifier`, `verdictOf_eq_executableVerifier`, `verdictOf_eq_leanVerifier` and `executableVerifier_eq_leanVerifier_stored`, in the same namespace), and no other file imports it. All runs reported below were made without this file, at the checksum c06b37e6bf53ef5577cdb397c9835c363eef30d5753ce514659c18d1b34da87a, with `scripts/check.py` and its lists as they were then. Wherever this page speaks of this repository's files or Lean files, of `lean/`, of the library, or of all its modules or declarations, this file is not included. For the file, three of the script's lists were extended afterwards (`scripts/top-theorems.txt` by four lines, `scripts/claimed-theorems.tsv` by four rows, `scripts/front-statements.txt` by four stored statements, 184 then and 188 now), three pinned values in `check.py` were updated (the number of theorems of the kind "general", from 10,772 to 10,776; the checksum of `front-statements.txt`; the checksum of the list of modules under `AtFullSide/`, from 914 modules to 915), and five figures in comments and in `scripts/RULES.txt` follow these counts. Nothing else in the script, its lists or its rules changed. With the file, `python3 -B scripts/check.py --digest` prints 620d8930cb09859399d9a75a15878550ee98c6a4b57753f560e33a04c515f5f5. The file was checked separately. It was compiled against a copy of the compiled files of the build in seven calls described below (`LEAN_NUM_THREADS=4 lake build AtFullSide.Face.ExecutableVerifierIsLeanVerifier`): exit status 0, with no error and no message about `sorry`; Lake compiled this one module and took every other compiled file as it was. Its compiled file was then replayed through Lean's kernel, outside the script, with the call that `check.py` uses for a module under `AtFullSide/` (`lake env lean --tstack=131072 --stdin`, which runs `replayFromImports` on the module): exit status 0. `lake env leanchecker -v` on the module also ended with exit status 0. For the definition and for each of the four theorems Lean reports the axioms `propext`, `Classical.choice` and `Quot.sound`, and no other. The steps `tree`, `words` and `imports` of the updated `scripts/check.py` pass over all files, this one included.

One whole run of the library's full check (`scripts/check.py`) over the Lean library in `lean/` has the last line "All steps passed: tree, words, imports, build (kernel replay, audit). …", at the checksum c06b37e6bf53ef5577cdb397c9835c363eef30d5753ce514659c18d1b34da87a. That line also says that no theorem got a verdict on binders or on `Classical.choice`: every line of `scripts/top-theorems.txt` says "general" (what that word means there: the head of that file). It says, too, that at least 7,888 declarations that program Lean (macros, notations, elaborators) stand in the modules below one named theorem ([GAPS.md](GAPS.md), 18 (c)). It is one run, on one machine. In its kernel replay 1,438 modules go by another call than `leanchecker` ([GAPS.md](GAPS.md), 73 (h)); Mathlib and the other packages are taken as they were compiled beforehand, and are not replayed ([GAPS.md](GAPS.md), 81 (g)); the 13 files under `Ask/` are read by the text steps alone. The script runs no mutation tests and no second, independent proof checker. The Lean community's `comparator` and `lean4lean` have not been run over these files.

The line, whole: "All steps passed: tree, words, imports, build (kernel replay, audit). This script runs no mutation tests and no second, independent proof checker (see lean/scripts/README.md). The result is about the compiled definitions: read the listing, not the source; the kernel replay took 1438 modules by another call than leanchecker: see the lines above (at least 7888 declarations program Lean in the modules below one named theorem); no theorem got a verdict on binders or on Classical.choice (every line of top-theorems.txt says general)"

In the full check's run one call of Lake (`lake build Library AtFullSide ShapeLines`, with LEAN_ABORT_ON_PANIC=1 and LEAN_NUM_THREADS=72 in the call's environment) builds the three libraries from nothing, in a copy of this repository's `lean/`, on one machine, held to 960 GiB of memory: exit status 0; it compiles 29,549 files; no message about `sorry`. The compiled files of Mathlib and the other packages are those that were compiled beforehand, copied in; the run compiles none of them.

In the same run the audit ends "ALL PASSED" over the build that the run makes: all 592,112 declarations in all 29,549 modules of the library, and all 9,883 copies of theorems that stand in more than one module, depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`. The script then finds the printed statements of 184 theorems the same, to the letter, as those stored in `scripts/front-statements.txt`. The 184 stored statements are Lean's own print over a build of Lean files that differ from this repository's nowhere but in comments, in docstrings and in the text of 43 strings; none was stored from this build's listing.

The other results of this page stand on another build of the same files, at the same checksum. It compiles the library's own files from nothing, in seven calls of Lake in one copy of these files. The last call, over all three libraries (`LEAN_ABORT_ON_PANIC=1 LEAN_NUM_THREADS=72 lake build Library AtFullSide ShapeLines`), compiles 28 modules anew and takes the compiled file of every other module from the calls before it: each of the library's 29,549 modules is compiled in exactly one of the calls. Each call ends with exit status 0, with no error and no message about `sorry`. Before the first call that copy holds no compiled file of the library. It holds those of Mathlib and the other packages, compiled beforehand ([GAPS.md](GAPS.md), 81 (g)), and the build compiles none of them. Its Lake files are this repository's.

Over that build these have run: the print of the names in the table below, each with the axioms that Lean reports for it; the two lines of [CHECKING.md](CHECKING.md), "The six theorems, and eight more" (exit status 0; each of the fourteen names answered); a walk over the constants beneath twenty named theorems, proofs included (what it finds: [GAPS.md](GAPS.md), 73 (h), last paragraph; [LIMITS.md](LIMITS.md), L69). `scripts/check_stored_examples.py`, which reads Lean files and looks at no compiled file, has run over the seven Lean files and the six example files that it names, all as they are in this repository ([CHECKING.md](CHECKING.md), "The stored files and the examples", gives the two calls and what a pass is worth): exit status 0, all 90 comparisons hold, 11 of them with an example file; with `--self-test`, exit status 0, 153 changes, each with the outcome that the program expects. The independent checker and the Lean verifier's reference run: under the table.

The checksum is what `python3 -B scripts/check.py --digest`, run in `lean/`, printed before that file was added; with the file it prints the second value given at the top of this page. It covers all 29,562 Lean files (29,563 with that file), among them those of `ShapeLines/` and the 13 under `Ask/` (these 13 belong to no library), and ten files under `scripts/` (nine lists and RULES.txt). It does not cover the Lake files (lakefile.toml, lake-manifest.json, lean-toolchain), nor check.py and its two helpers (lclib.py, Audit.lean.in), nor `scripts/check_stored_examples.py`, nor files that check.py leaves out of the library. If it prints something other than that second value for you, this page is not about your files.

The names printed, each with the axioms that Lean reports for it: none beyond `propext`, `Classical.choice` and `Quot.sound`. The names are those that the writers of these pages asked for; this table is the only list of them. "yes" in the third column says only that Lean found the name in that build; a name that Lean did not find has no row.

| name | module | built | axioms that Lean prints |
|---|---|---|---|
| `AtFull.Top.sound_zFull` | `Johnson.AtFull.Top.SoundAtStored` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.mostWork_zFull` | `AtFullSide.E2E.SoundAsIOPNumbersAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.probability_zFull` | `AtFullSide.E2E.SoundAsIOPNumbersAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.probability_zFull_79` | `AtFullSide.E2E.SoundAsIOPNumbersAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.rounds_zFull` | `AtFullSide.E2E.SoundAsIOPNumbersAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.soundAsIOP_protocol_zFull` | `AtFullSide.E2E.SoundAsIOPAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.soundAsIOP_zFull` | `AtFullSide.E2E.SoundAsIOPAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.AtFiles.wholeRun_zFull` | `AtFullSide.E2E.SoundAsIOPAtWritten` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Frames.shape_of_form` | `AtFullSide.Frames.LastChain` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Home.lastFits_idle_named` | `AtFullSide.Home.HomeAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.TheKeyLetters.offlineDebts_at_the_files` | `E2E.LotKeyAcceptsAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.aDueListWithNoStop_in_scope` | `AtFullSide.Honest.CompleteInScopeNotForNothing` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.a_tied_request_exists` | `AtFullSide.Honest.TheOneObject` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.a_tied_run_exists` | `AtFullSide.Honest.TheOneObject` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.atEveryTiedRunAtItsThreads` | `AtFullSide.Honest.TheOneObject` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.complete_at_the_files` | `AtFullSide.Honest.CompleteAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.complete_at_the_stored_files_whole` | `AtFullSide.Honest.CompleteAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.complete_in_scope` | `AtFullSide.Honest.CompleteAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.complete_in_scope_with_a_served_request` | `AtFullSide.Honest.CompleteInScopeNotForNothing` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.every_served_request_is_tied` | `AtFullSide.Honest.TheOneObject` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Honest.someRequestIsServed_in_scope` | `AtFullSide.Honest.CompleteInScopeNotForNothing` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K1.owner_fresh_at_return` | `AtFullSide.K1.GoodAtReturn` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K12.ground_at_head` | `AtFullSide.K12.GroundAtHeadW` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K12.hone_at_head` | `AtFullSide.K12.LettersHone` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K12.w_ready_at_fold` | `AtFullSide.K12.LettersReadyW` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K13.k13_wHeard_at_head` | `AtFullSide.K13.WFillAtHead` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K13.layers_plans_are_there` | `AtFullSide.K13.NotTakenAtTheReturn` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K13.q0_is_idle` | `AtFullSide.K13.NotTakenAtTheReturn` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K14.first_door_at_end` | `AtFullSide.K14.FirstDoorAtEnd` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K14.k14_row_at_return` | `AtFullSide.K14.RowIsWholeAtServedRuns` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.K2.simulatorAtTheBase` | `AtFullSide.K2.SimulatorAtTheBaseProof` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.bindsAt_zAt` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.bindsAt_zFull` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.extractsCommitted_zAt` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.extractsCommitted_zFull` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.noTwoOpenings_zAt` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.noTwoOpenings_zFull` | `AtFullSide.Bind.TheTieAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.premises_zFull` | `AtFullSide.Bind.LiveAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Tie.premises_zGap` | `AtFullSide.Bind.LiveAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Top.theLive_zAt` | `AtFullSide.Top.LiveAtPolicies` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Top.theLive_zFull` | `AtFullSide.Top.LiveAtFull` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Top.theLive_zGap` | `AtFullSide.Top.LiveAtPolicies` | yes | propext, Classical.choice, Quot.sound |
| `AtFullSide.Top.written_zFull` | `AtFullSide.Top.WrittenAtFull` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.AtHonestTables.extract_at_served` | `E2E.ExtractorAtHonestTables` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.CompleteOnServedRequests` | `E2E.CompleteAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.ConclusionFails` | `E2E.SoundAsIOPProbabilityAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles` | `E2E.CompleteAsIOPAtNamed` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.honestProvers` | `E2E.TheHonestProver` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.noDefaultBites` | `E2E.KeyNoDefaultBites` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.offlineTestOnOmega_there` | `E2E.KeyOfflineSides` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok` | `E2E.KeyThePartsFacts` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.HonestTerm.thePartsAt` | `E2E.KeyArgumentsAt` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.InScopeSetting.sample_and_johnson_in_scope` | `E2E.SampleAndJohnsonInScope` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.ServedRequest` | `E2E.CompleteAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.Statements.clearedIsUniformOnPassing` | `E2E.SoundAsIOPProbabilityAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.Statements.relationMeans` | `E2E.SoundAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.Statements.verifiersAskTheWork` | `E2E.SoundAsIOPProbabilityAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.Statements.wholeRunAtFiles` | `E2E.SoundAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.bound_le_79` | `E2E.SoundAsIOPNumbers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.clearedIsUniformOnPassing` | `E2E.SoundAsIOPProbabilityAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.clearingIsTheWires` | `E2E.SoundAsIOPProbabilityAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.completenessTarget` | `E2E.CompleteAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.mostWorkInScope` | `E2E.SoundAsIOPNumbers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.not_hidE_own` | `E2E.ObjectGuardsSeeded` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.object_description` | `E2E.DescriptionTie` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.probabilityInScope` | `E2E.SoundAsIOPNumbers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.probabilityInScope79` | `E2E.SoundAsIOPNumbers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.protocolAtFiles` | `E2E.BridgeJoinAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.read_of_inScope` | `E2E.HeadAtLaid` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.relationAtFiles` | `E2E.SoundAsIOPAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.roundsInScope` | `E2E.SoundAsIOPNumbers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.servedRequest_at_every_prompt` | `E2E.CompleteAtEveryWellFormedRequest` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.servedRequest_of_result` | `E2E.CompleteAtEveryWellFormedRequest` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.soundAsIOPAtFiles` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.soundAsIOPAtFiles_provers` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.soundAsIOPAtTheProtocol` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.tables_own` | `E2E.TablesAtOwnObject` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.tables_own_named` | `E2E.TablesAtOwnObject` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.third_public` | `E2E.KeyPublic` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.verifiersAskTheWork` | `E2E.SoundAsIOPWorkIsTheVerifiers` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.wholeRunAtFiles` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.whole_atFiles` | `E2E.WholeViewAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.AtFiles.workFaithful_atFiles` | `E2E.CompleteAsIOPWorkBits` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.bitsE_listed` | `E2E.LinkLaidPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.laid_accepted` | `AtFullSide.E2E.LinkLaidAccepted` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.laid_hashed_accepted` | `AtFullSide.E2E.LinkLaidHashedAccepted` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.linkLaidAtOnce` | `E2E.LinkLaidPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.linkLaidEight` | `E2E.LinkLaidAllAtOnce` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.linkLaidWithBound` | `E2E.LinkLaidPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.premW_laid` | `E2E.LinkLaidPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.LinkLaid.zeta_of_twelve` | `E2E.LinkLaidPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OfflineRows.offline_clauses_at_the_files` | `E2E.OfflineClausesAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.ThreeAtFiles` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.ThreeAtOneProtocol` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.link_prover_inside` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.offline_at_one_protocol` | `E2E.OneProtocolAtTheEnds` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.offline_prover_inside` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.protocol_is_the_compiled_verifiers` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.statements_of_threeAtOne` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.threeAtOne_of_statements` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.verifiers_at_every_provers` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.work_clears_as_soundness` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.OneProtocol.work_passes_as_soundness` | `E2E.ThreeAtOneProtocol` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.fiveLeft_fixed` | `E2E.FiveLeftSilentCaps` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.hasSilentMemberC_description` | `E2E.FiveLeftSilentCaps` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.noProverSide_description` | `E2E.PremisesAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.not_noProverSide_copy` | `E2E.PremisesAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.not_noProverSide_session` | `E2E.PremisesAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.privacyFromFive_description` | `E2E.PrivacyAtDescription` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Premises.readsG_atFiles` | `E2E.PremisesAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Reads.hidE_filesAt` | `E2E.ReadsAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Reads.reads_filesAt_scope` | `E2E.ReadsAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Shown.allAtOnce_description` | `E2E.StringsOpenInGame` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Shown.keyInGame_description` | `E2E.StringsInGame` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Shown.sessionsInGame_description` | `E2E.SessionsInGame` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.answer_bijective` | `E2E.TableMasked` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.every_set_filesAt` | `E2E.TableHidesGuardAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.every_set_objAt` | `E2E.TableHidesGuardAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.hides_full` | `E2E.TableHides` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.masked_cells` | `E2E.TableMasked` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.not_hidE_filesAt` | `E2E.TableHidesGuardAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.rowsOf_laws` | `E2E.TableMasked` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.strong_codingHonest` | `E2E.TableStrong` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.Table.table_law` | `E2E.TableStrong` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.privacyWithBound_description` | `E2E.ZetaAtCaps` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.privacyWithNumber_description` | `E2E.ZetaAtCaps` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.sMT_description` | `E2E.ZetaSalt` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.twelve_description` | `E2E.ZetaAtInput` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.zetaW_le_caps` | `E2E.ZetaCaps` | yes | propext, Classical.choice, Quot.sound |
| `AtPublicFiles.ZetaAt.zeta_number_caps` | `E2E.ZetaAtCaps` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.bindsAt` | `Johnson.Bind.Cpp.TheTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.bindsAtZ_cpp` | `Johnson.Bind.Cpp.OfTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.bindsWith_of_tieAt` | `Johnson.Bind.Cpp.OfTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.blindDoesNotBind` | `Johnson.Bind.Cpp.Controls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.blindTwin_exact_join_and_complete` | `Johnson.Bind.Cpp.JoinControls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.blindTwin_fails` | `Johnson.Bind.Cpp.Controls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.blind_extracts` | `Johnson.Bind.Cpp.Controls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.blind_twoOpenings` | `Johnson.Bind.Cpp.Controls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.commit_D₀` | `Johnson.Bind.Cpp.JoinControls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.commit_count` | `Johnson.Bind.Cpp.OfTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.extractsCommitted` | `Johnson.Bind.Cpp.TheTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.extractsCommitted_square_salt` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.extracts_salt` | `Johnson.Bind.Cpp.TheTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.extracts_square_salt` | `Johnson.Bind.Cpp.TheTie` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.hollow_meets_join` | `Johnson.Bind.Cpp.JoinControls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.hollow_meets_join_never` | `Johnson.Bind.Cpp.JoinControls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.honest_count` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.noTwoOpenings_live` | `Johnson.Bind.Cpp.NoTwoOpeningsAtLive` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.rejects_of_dead` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.saltAt_of_live` | `Johnson.Bind.Cpp.SaltAt` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.sample_D₀` | `Johnson.Bind.Cpp.JoinControls` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.soundAtCommitted` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.soundAtCommitted_exact` | `Johnson.Bind.Cpp.SoundAtCommittedExact` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.soundAtCommitted_exact_nonempty` | `Johnson.Bind.Cpp.SoundAtCommittedExact` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.soundAtCommitted_own` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.soundAtCommitted_square` | `Johnson.Bind.Cpp.SoundAtCommitted` | yes | propext, Classical.choice, Quot.sound |
| `Bind.Cpp.tieAt` | `Johnson.Bind.Cpp.TheTie` | yes | propext, Classical.choice, Quot.sound |
| `Cb.BCHKS46At` | `Cb.Gen.CodeListRSAt` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Bridge.bchks46At` | `Cb.Bridge.CodeListRSProved` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Bridge.foldErr_ix` | `Johnson.Bridge.FoldErrIx` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Gl.Bld.J.cnt_32_446693374_2852142980_132` | `Johnson.T2.Idx` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Gl.Wf8.placesW` | `Cb.GlVal.GlToyWfItem` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Gl.bchks46At` | `Cb.Bridge.GlCodesProved` | yes | propext, Classical.choice, Quot.sound |
| `Cb.Pv.SendLoc.errs` | `Cb.Pv.Switch.SendLoc` | yes | propext, Classical.choice, Quot.sound |
| `Cb.cnt_ldSwBad1` | `Cb.Ld.LdSwitchWordsProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.cnt_ldSwBad2` | `Cb.Ld.LdSwitchWordsProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.johnson_tables` | `Cb.Gen.JohnsonListProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.johnson_tables_cnt` | `Cb.Gen.JohnsonListProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldBase_good` | `Cb.Ld.LdBaseProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldFc_overF` | `Cb.Ld.LdFoldEqCodeProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldRng_err` | `Cb.Ld.LdRngProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldRng_goodT` | `Cb.Ld.LdRngProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldSendFam_cnt` | `Cb.Ld.LdSendFamProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ldSwitch_know` | `Cb.Ld.LdSwitchProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.ld_sum_know` | `Cb.Ld.LdSumKnowProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.psc_know` | `Cb.Ld.LdPscProofsIor` | yes | propext, Classical.choice, Quot.sound |
| `Cb.rows_avoid` | `Cb.Ld.LdRelRowsEAbsProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.rows_cost_nothingAt` | `Cb.Gen.CodeListRSAtProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cb.rows_free_abs` | `Cb.Ld.LdRelRowsEAbsProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cm.TI.eq_of_dvd` | `Inst.Model.Bound.Base` | yes | propext, Classical.choice, Quot.sound |
| `Cm.TP.Lay.stream_eqK` | `Cm.TargetPLayers` | yes | propext, Classical.choice, Quot.sound |
| `Cm.target_p_guards` | `Cm.TargetPLangsProofs` | yes | propext, Classical.choice, Quot.sound |
| `Cm.true_next` | `Cm.RelTrue` | yes | propext, Classical.choice, Quot.sound |
| `Cm.true_pos` | `Cm.RelTrue` | yes | propext, Classical.choice, Quot.sound |
| `Cm.true_unique` | `Cm.RelTrue` | yes | propext, Classical.choice, Quot.sound |
| `Code.cnt_bad_eqk_mul_sum` | `Code.Derived` | yes | propext, Classical.choice, Quot.sound |
| `Compile.Batch.mainBatchKE2` | `CompileK.Defer2Main` | yes | propext, Classical.choice, Quot.sound |
| `Compile.LiveW.pureZ` | `Compile.LiveWalk` | yes | propext, Quot.sound |
| `Desc.K14.Law.bad_le_efReal` | `Johnson.Goal.Numbers.K14BadAt` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.k14_at_free_head` | `Johnson.Desc.K14.Law.LedgerAtFreeHead` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.k14_rounds_real` | `Johnson.Goal.Numbers.K14RoundsAt` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.ownPt_below` | `Johnson.Goal.Numbers.K14OwnAllAt` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.point_leadsB_at_k14` | `Johnson.Desc.Sound.PointAtK14` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.real_test64` | `Johnson.Goal.Numbers.K14JointAt` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K14.Law.teeth` | `Johnson.Goal.Numbers.K14RoundsAt` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K15.H_fullV` | `Johnson.Desc.K15.HsemAtV` | yes | propext, Classical.choice, Quot.sound |
| `Desc.K15.foldV` | `Johnson.Desc.K15.SendOwnLaw` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.G9_theWider` | `Johnson.Goal.Conditions.WiderAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.backThe` | `Johnson.Goal.Conditions.BindsAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.bindsWith_plain_law` | `Johnson.Goal.Conditions.BindsTold` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.bytes_forty` | `Johnson.Goal.Conditions.HomeSalt` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.caps_home` | `Johnson.Goal.Conditions.NumberAtHome` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.compilerSoundnessConditions_layoutsByPublicReading` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.completeOn_end` | `Johnson.Goal.Conditions.HomeEnd` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.completeOn_last` | `Johnson.Goal.Conditions.HomeLast` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.entrySound` | `Johnson.Goal.Conditions.EntrySits` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.entrySound_theLay` | `Johnson.Goal.Conditions.NumbersAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.hole_entrySound` | `Johnson.Goal.Conditions.EntrySits` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.innerCompiledVerifier_no_build` | `Johnson.Goal.Tie.DescriptionOfDataRefuse` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.keySound_theLay` | `Johnson.Goal.Conditions.NumbersAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.lastFits_idle` | `Johnson.Goal.Conditions.HomeIdle` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.layoutsByPublicReading_code` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.layoutsByPublicReading_noCoin` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.layoutsByPublicReading_once` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.layoutsByPublicReading_spare` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.layoutsByPublicReading_word` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.linkFits_at` | `Johnson.Goal.Conditions.LinkFitsAt` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.meaning_the` | `Johnson.Goal.Conditions.SoundAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.number_home` | `Johnson.Goal.Conditions.NumberAtHome` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.proofSound_theLay` | `Johnson.Goal.Conditions.NumbersAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.protocolDataWellFormed` | `Johnson.Goal.Description.Live` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.publicReadingFitAtDescriptionOfFields` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFieldsO` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.queryBound_home` | `Johnson.Goal.Conditions.HonestAtHome` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.readingsQueryBound_descriptionOfFields` | `Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.sec_the` | `Johnson.Goal.Conditions.BindsAtThe` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.three_le_idleAlpha` | `Johnson.Goal.Conditions.HomeIdle` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.verify_record` | `Johnson.Goal.Conditions.WiderComplete` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.verify_refuses_empty` | `Johnson.Face.EmptyProof` | yes | propext, Classical.choice, Quot.sound |
| `FlashProve.written_or_no_all` | `Johnson.Goal.Description.KeyWritten` | yes | propext, Classical.choice, Quot.sound |
| `Fmt.Declared.settingOk` | `Fmt.Parsed` | yes | none |
| `Fmt.TableShape.ok` | `Fmt.Parsed` | yes | none |
| `Fmt.size_oracle` | `Fmt.Rules23Laws` | yes | propext, Classical.choice, Quot.sound |
| `H2K.Sizes.inScope_readFiles` | `Johnson.Desc.K12.Law.Sizes.StageSizesAtScope` | yes | propext, Classical.choice, Quot.sound |
| `H2K12.lastTypedAt_at_head` | `Johnson.Loose.H2K12.K12AtFree` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.EnvF.Adm` | `Hiop.Seeded.Form` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.HostF.view` | `Hiop.Seeded.Form` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.ViewNearF` | `Hiop.Seeded.Form` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.form_laws` | `Hiop.Seeded.FormProof` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.lifeSeededAt` | `Hiop.Seeded.AtIndex` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.simWholeF` | `Hiop.Seeded.Form` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.Seeded.whole_all_seeds` | `Hiop.Seeded.WholeProof` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.rec_answers_uniform` | `Hiop.RecRows` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.rec_hides_law` | `Hiop.RecRows` | yes | propext, Classical.choice, Quot.sound |
| `Hiop.rec_hides_of_rows` | `Hiop.RecRows` | yes | propext, Classical.choice, Quot.sound |
| `IM.laid_planOk` | `Johnson.IMR.SeatForm` | yes | propext |
| `IM.yes_laid` | `Johnson.IMR.SeatForm` | yes | propext |
| `Inst.Model.polTests_iff` | `Inst.Model.Scales` | yes | propext, Quot.sound |
| `IntegerModel.isModelOutput_of_isTrueRequest` | `IntegerModel.ModelOutput` | yes | propext, Classical.choice, Quot.sound |
| `IntegerModel.isTrueRequest_of_canServe` | `IntegerModel.ModelOutput` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.LeastBoundNumbers.Hold` | `IntegerModel.Bounds.LeastBoundCheck` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_boxWorstCaseCheck` | `IntegerModel.Bounds.NeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_frobeniusLeastBoundCheck` | `IntegerModel.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_frobeniusLengthCheck` | `IntegerModel.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_leastBoundNumbersPassScaledGramTest` | `IntegerModel.Bounds.ScaledGramTestOfLeastBoundNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_leastBoundWorstCaseCheck` | `IntegerModel.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_lengthWorstCaseCheck` | `IntegerModel.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassGramTest` | `IntegerModel.Bounds.GramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassScaledGramTest` | `IntegerModel.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassSmallerSideGramTest` | `IntegerModel.Bounds.SmallerSideGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.control_fails_with_frobenius` | `IntegerModel.Bounds.LengthCheckControl` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.control_leastBound_passes_with_zeros` | `IntegerModel.Bounds.LeastBoundCheckControl` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.control_leastBound_zeros_do_not_hold` | `IntegerModel.Bounds.LeastBoundCheckControl` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.control_model_eq_none` | `IntegerModel.Bounds.LengthCheckControl` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.control_passes_with_zeros` | `IntegerModel.Bounds.LengthCheckControl` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.control_wellFormed` | `IntegerModel.Bounds.LengthCheckControl` | yes | propext |
| `IntegerTransformer.Bounds.control_zeros_do_not_hold` | `IntegerModel.Bounds.LengthCheckControl` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.dual_coordinate` | `IntegerModel.Bounds.DualColumnBound` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.frobeniusLeastBoundCheck_of_frobeniusLengthCheck` | `IntegerModel.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.frobeniusLeastBoundNumbers_hold` | `IntegerModel.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.frobeniusStretchNumbers_hold` | `IntegerModel.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.frobeniusStretchNumbers_within` | `IntegerModel.Bounds.UniformLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.hold_of_leastBoundNumbersPassScaledGramTest` | `IntegerModel.Bounds.ScaledGramTestOfLeastBoundNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.hold_of_stretchNumbersPassGramTest` | `IntegerModel.Bounds.GramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.hold_of_stretchNumbersPassScaledGramTest` | `IntegerModel.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.hold_of_stretchNumbersPassSmallerSideGramTest` | `IntegerModel.Bounds.SmallerSideGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.le_leastOver` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.leastBoundNumbersOf_hold` | `IntegerModel.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.leastBoundWorstCaseCheck_of_lengthWorstCaseCheck` | `IntegerModel.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.leastBound_of_length` | `IntegerModel.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.lengthWorstCaseCheck_of_uniformLengthCheck` | `IntegerModel.Bounds.UniformLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.length_mean` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.length_of_blocks` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.length_of_stretchBoundOf` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.magnitude_gateKeyOf_le` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.magnitude_inner_le_dual` | `IntegerModel.Bounds.DualColumnBound` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.magnitude_silu_read_le` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.norm_out_inBall` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.pair_squares_le` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.product_read_le_leastColumnBound` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.quadraticForm_le_of_scaledChainFits` | `IntegerModel.Bounds.ScaledGramIteration` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.routedExpert_input_inFineBall` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.scaledGramIterationFitsOf_nil` | `IntegerModel.Bounds.ScaledGramIteration` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.stretchBoundOf_of_gramIterationFitsOf` | `IntegerModel.Bounds.GramIteration` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBoundOf_of_gramIterationFitsOnSmallerSideOf` | `IntegerModel.Bounds.StretchOfTranspose` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBoundOf_of_scaledGramIterationFitsOf` | `IntegerModel.Bounds.ScaledGramIteration` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBoundOf_of_scaledGramIterationFitsOnSmallerSideOf` | `IntegerModel.Bounds.StretchOfTranspose` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBoundOf_of_transpose` | `IntegerModel.Bounds.StretchOfTranspose` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBound_of_gramIterationFits` | `IntegerModel.Bounds.GramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBound_of_scaledGramIterationFits` | `IntegerModel.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchBound_of_scaledGramIterationFitsOnSmallerSide` | `IntegerModel.Bounds.SmallerSideGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `IntegerTransformer.Bounds.stretchNumbersPassScaledGramTest_noLevels` | `IntegerModel.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Quot.sound |
| `IntegerTransformer.Bounds.turn_square_le` | `IntegerModel.Bounds.LeastBoundLemmas` | yes | propext, Classical.choice, Quot.sound |
| `Iop.Doomed.append` | `Iop.Rbr` | yes | propext, Classical.choice, Quot.sound |
| `Iop.FailsAt` | `Hiop.CompleteCore` | yes | propext, Quot.sound |
| `Iop.FailsRarely` | `Hiop.CompleteCore` | yes | propext, Classical.choice, Quot.sound |
| `Iop.GChal.cnt_pass` | `Iop.GrindProofs` | yes | propext, Classical.choice, Quot.sound |
| `Iop.HolographicProtocol.WholeRun` | `Hiop.SoundAsIOP` | yes | propext, Quot.sound |
| `Iop.HolographicProtocol.WholeRun.Accepted` | `Hiop.SoundAsIOP` | yes | propext, Quot.sound |
| `Iop.HolographicProtocol.WholeRun.Concludes` | `Hiop.SoundAsIOP` | yes | propext, Quot.sound |
| `Iop.HolographicProtocol.wholeRunShape` | `Hiop.SoundAsIOP` | yes | propext, Quot.sound |
| `Iop.PartsWork.Faithful` | `Hiop.CompleteCore` | yes | propext, Classical.choice, Quot.sound |
| `Iop.Reduction.Leads.seq` | `Johnson.Desc.Plain.Leads` | yes | propext, Classical.choice, Quot.sound |
| `Iop.Spec.goodT_seq_masked` | `Ior.KnowCollRulesMask` | yes | propext, Classical.choice, Quot.sound |
| `Iop.chanceAtPassing` | `Hiop.CompleteCore` | yes | propext, Classical.choice, Quot.sound |
| `Iop.goodT_seq_masked` | `Ior.KnowCollRulesMaskProofs` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.AtFull.Shape.first_chain_whole` | `Johnson.AtFull.Shape.Scope.FirstChainWhole` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.AtFull.Shape.link_yes` | `Johnson.AtFull.Shape.SwitchReturns` | yes | propext, Quot.sound |
| `Johnson.AtFull.Shape.testV` | `Johnson.AtFull.Shape.TestReturnsFrame` | yes | propext, Quot.sound |
| `Johnson.Bridge.AtPlan.below_and_in_johnson` | `E2E.StagesAtOrBeyondHalfTheDistance` | yes | propext |
| `Johnson.Bridge.AtPlan.count` | `E2E.StagesAtOrBeyondHalfTheDistance` | yes | propext |
| `Johnson.Bridge.AtPlan.stage_at_or_beyond_half_the_distance` | `E2E.StagesAtOrBeyondHalfTheDistance` | yes | propext |
| `Johnson.Face.everyRandomness_termHonest` | `AtFullSide.Face.FinalBindingOpeningsAtHonestProversAndSettingsOf` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.G.PackArms.counts` | `Johnson.G.PackLitArms` | yes | propext |
| `Johnson.G.PackArms.every_message_is_within_johnson_and_at_or_beyond_half` | `Johnson.G.PackLitArms` | yes | propext, Quot.sound |
| `Johnson.Prover.Link.accLaw_link` | `Johnson.Prover.Link.LinkFrame` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.Prover.Link.door_premises` | `Johnson.Prover.Link.DoorPay` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.Prover.Link.door_yes` | `Johnson.Prover.Link.FormDoorLaws` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.Prover.Link.foldCuts_of_nums` | `Johnson.Prover.Link.FormFoldPlan` | yes | propext, Quot.sound |
| `Johnson.Prover.Link.linkYes_of` | `Johnson.Prover.Link.LinkJoinE` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.Prover.Link.link_yes` | `Johnson.Prover.Link.LinkJoinF` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.RunOne.Sound.desc_lists` | `Johnson.RunOne.Sound.KeyListsAtFK` | yes | propext, Classical.choice, Quot.sound |
| `Johnson.RunOne.Sound.laid_rounds_in_scope` | `Johnson.RunOne.Sound.KeyListsInScope` | yes | propext, Classical.choice, Quot.sound |
| `LPFD.Full.fitsD` | `Johnson.Flat.Told.Dec.TAtLaws` | yes | propext, Classical.choice, Quot.sound |
| `LPFD.Full.laidPOf_pins_scope` | `Johnson.Goal.Numbers.LaidPinsInScope` | yes | propext, Classical.choice, Quot.sound |
| `LPFD.Full.laidPOf_written` | `Johnson.Desc.Laid.ProofFullScope` | yes | propext, Classical.choice, Quot.sound |
| `LPFD.keyDebtCap_of_21` | `Johnson.Top.Fire.Code.The35` | yes | propext, Classical.choice, Quot.sound |
| `LPFD.keySound_of_debt` | `Johnson.Top.Fire.Code.KeyDebt` | yes | propext, Classical.choice, Quot.sound |
| `Meaning.layersSay` | `Johnson.Goal.Meaning.LayersSay` | yes | propext, Classical.choice, Quot.sound |
| `Meaning.means_of_served` | `Johnson.Goal.Meaning.ServedMeans` | yes | propext, Classical.choice, Quot.sound |
| `Meaning.served_met` | `Johnson.Goal.Meaning.ServedMeans` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Flat.CarryS.doomed` | `OnBytes.Flat.CarrySkip` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Flat.KeepsOf.OnBytes.linkVerify` | `OnBytes.Flat.BlocksKeep` | yes | propext, Quot.sound |
| `OnBytes.Flat.Maps.below_err` | `OnBytes.Flat.CarrySMaps` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Flat.entryFull_seedLawK` | `OnBytes.Flat.RecordSeed` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.FrontRoad.familyLaws_the` | `Johnson.FrontRoad.AtBuiltNamed` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.FrontRoad.inRange_backThe` | `Johnson.FrontRoad.RangeOf` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.HonestTrace.TwoIndicesServe.twoIndicesServeOneRequest` | `Johnson.HonestTrace.Joint.TwoIndicesServeOneRequest` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.K.Arm.encId_hasCode` | `Johnson.TypedOracleCompiler.Top.IdSeedHasCode` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.K.Arm.room_recordGround` | `Johnson.TypedOracleCompiler.Top.IdSeedHasCode` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.K.Arm.room_smallRecordGround` | `Johnson.TypedOracleCompiler.Top.IdSeedHasCode` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.LinkSim.AtHome.homeExactAt` | `Johnson.LinkSim.AtHome.HomeExactAll` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.LinkSim.AtHome.homeSide_accepted` | `Johnson.LinkSim.AtHome.HomeAccepted` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.LinkSim.AtHome.home_beside` | `Johnson.LinkSim.AtHome.HomeTies` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.LinkSim.AtHome.home_withheld` | `Johnson.LinkSim.AtHome.TwoViews` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Params.linOk_ok` | `OnBytes.Params.Fit.TreesSized` | yes | propext |
| `OnBytes.Params.record_radius_inJohnson` | `OnBytes.Params.RecordRound` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Prover.CompleteAtEveryCoin` | `Johnson.Prover.All.CompleteAsIOPForTheCompiler` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Prover.home_yes` | `Johnson.Prover.Home.Yes` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Road.K4.Plan4.herr_cap` | `Johnson.Road.K4.CapFromMeets` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Road.L5.sound_ledger` | `Johnson.Road.Lane5SoundLedger` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Slice.coll_count_of_list` | `OnBytes.Slice.RecordColl` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Slice.fr_bound` | `OnBytes.Flat.EntryRecord` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Slice.fr_link_sound_own` | `OnBytes.Slice.FullRecTable` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Slice.list_johnson` | `OnBytes.Slice.LinkRecBchks` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.Slice.recZ_okOn` | `OnBytes.Slice.RecordOK` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.bundle_argW` | `Johnson.WholeKey.Bundle` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.complete_argW` | `Johnson.WholeKey.Complete` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.complete_of_honFit` | `Johnson.WholeKey.CompleteOfRecs` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.extEnc_silent` | `Johnson.WholeKey.Foes` | yes | propext, Quot.sound |
| `OnBytes.WholeKey.silent_good` | `Johnson.WholeKey.Foes` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.wholeKeyPrivacy` | `Johnson.WholeKey.Main` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.WholeKey.wholeKeySchemeOverTypedOracles_V` | `Johnson.WholeKey.AtInput` | yes | propext, Classical.choice, Quot.sound |
| `OnBytes.formatHashFastForm_eq_formatHash` | `OnBytes.Hash.HEq` | yes | propext, Quot.sound |
| `P1K8T.draw_at_flat` | `Johnson.P1K8R.PieceAtRow` | yes | propext, Classical.choice, Quot.sound |
| `P1K8T.ground_at_head` | `Johnson.P1K8R.CondOfRest3` | yes | propext, Classical.choice, Quot.sound |
| `P1K8T.k08_piece_at_row` | `Johnson.P1K8R.PieceAtRow` | yes | propext, Classical.choice, Quot.sound |
| `P1K8T.k8Fence_at_head` | `Johnson.P1K8R.BlindFromHead` | yes | propext, Classical.choice, Quot.sound |
| `P1K8T.wt_back_at` | `Johnson.P1K8R.WtBack` | yes | propext, Classical.choice, Quot.sound |
| `P5J.AtMgA.lastLeft_at_head_alone` | `Johnson.P2LawR.LastLeftAlone` | yes | propext, Classical.choice, Quot.sound |
| `P5J.AtMgA.leads3_of_leftAt` | `Johnson.P5J.L0.LastLeftAt` | yes | propext, Classical.choice, Quot.sound |
| `P5J.LaidAt.laidPOf` | `Johnson.P5T.FenceAtMg` | yes | propext, Classical.choice, Quot.sound |
| `P5J.conds_of_laid` | `Johnson.Goal.Skeleton.CondsOfLaid` | yes | propext, Classical.choice, Quot.sound |
| `P5J.five_at_free2_laid2` | `Johnson.P5J.FiveAtFree2Laid2` | yes | propext, Classical.choice, Quot.sound |
| `P5J.good_of_kinds` | `Johnson.P5J.RowsAtMg` | yes | propext, Classical.choice, Quot.sound |
| `P5J.headA_at_name` | `Johnson.P5J.AtNameA` | yes | propext, Classical.choice, Quot.sound |
| `P5J.meansOfStart` | `Johnson.P5J.MeansQ` | yes | propext, Classical.choice, Quot.sound |
| `P5J.owed_of_live` | `Johnson.Goal.Skeleton.OwedOfLive` | yes | propext, Classical.choice, Quot.sound |
| `P5J.reply_leaves_at_mg` | `Johnson.P5J.ReplyLeavesAtMg` | yes | propext, Classical.choice, Quot.sound |
| `PV.Program.verdictOf_eq` | `Johnson.PVR.ProgramTotal` | yes | propext, Classical.choice, Quot.sound |
| `PV.Program.verdictOf_is_verify` | `Johnson.PVR.Program` | yes | propext, Classical.choice, Quot.sound |
| `PV.Program.verdictOf_map` | `Johnson.PVR.ProgramTotal` | yes | propext, Classical.choice, Quot.sound |
| `PV.Program.verdictOf_none` | `Johnson.PVR.Program` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.formAccepts_eq` | `Johnson.PVR.SoundOfTheFormEvents` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.soundOfDecision_accepts_iff` | `Johnson.PVR.SoundOfTheFormEvents` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.soundOfDecision_form_iff` | `Johnson.PVR.SoundOfTheFormEvents` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.sound_of_the_form_at` | `Johnson.PVR.SoundOfTheForm` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.sound_of_the_form_events` | `Johnson.PVR.SoundOfTheFormEvents` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.sound_of_the_form_events_oOf` | `Johnson.PVR.SoundOfTheFormEvents` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.theForm_accepts_only` | `Johnson.PVR.SoundOfTheForm` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.theForm_at_hash` | `Johnson.PVR.SoundOfTheForm` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.theForm_eq_verify` | `Johnson.PVR.SoundOfTheForm` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.theForm_total` | `Johnson.PVR.SoundOfTheForm` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.verdictThe_eq` | `Johnson.PVR.RideEveryHash` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.verdictThe_is_theDescription` | `Johnson.PVR.RideThe` | yes | propext, Classical.choice, Quot.sound |
| `PV.Ride.verdictThe_some` | `Johnson.PVR.RideEveryHash` | yes | propext, Classical.choice, Quot.sound |
| `Policy.TeethAll.every_output_at_meets_iff` | `Policy.Front.TeethAllChannels` | yes | propext, Classical.choice, Quot.sound |
| `Policy.card_gap_ge_mul_le_qExample` | `Policy.Front.MeetsPolicyAtGap` | yes | propext, Classical.choice, Quot.sound |
| `Policy.exists_policy_of_close_scales` | `Policy.Front.MeetsPolicyIdleAtScales` | yes | propext, Classical.choice, Quot.sound |
| `Policy.gaps_of_meetsPolicy_qExample_short` | `Policy.Front.MeetsPolicyAtGap` | yes | propext, Classical.choice, Quot.sound |
| `Policy.ledger_honest` | `Policy.Rel.LedgerRelLaws` | yes | propext, Classical.choice, Quot.sound |
| `Policy.ledger_lang` | `Policy.Rel.LedgerRelLaws` | yes | propext, Classical.choice, Quot.sound |
| `Policy.ledger_noWrap` | `Policy.Rel.LedgerRelLaws` | yes | propext, Classical.choice, Quot.sound |
| `Policy.ledger_relation_at_protocol_prime` | `Policy.Rel.LedgerRelLaws` | yes | propext, Classical.choice, Quot.sound |
| `Policy.ledger_sub` | `Policy.Rel.LedgerRelLaws` | yes | propext, Classical.choice, Quot.sound |
| `Policy.logitGap_eq_choice` | `Policy.Front.MeetsPolicyGuards` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_exact_iff` | `Policy.Front.MeetsPolicyGuards` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_iff_of_gapCeiling_le` | `Policy.Front.MeetsPolicyIdleAtScales` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_of_close_scales` | `Policy.Front.MeetsPolicyIdleAtScales` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_of_isModelOutput` | `Policy.Front.MeetsPolicyGuards` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_qExample_of_one_free` | `Policy.Front.MeetsPolicyAtGap` | yes | propext, Classical.choice, Quot.sound |
| `Policy.meetsPolicy_zeroWeights` | `Policy.Front.TrueUnder` | yes | propext, Classical.choice, Quot.sound |
| `Policy.modelNextToken_eq_firstArgmax` | `Policy.Front.MeetsPolicyGuards` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K1.baseMaker_returns` | `AtFullSide.K1.HeadAtBaseMaker` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K1.headAtReturn_baseMaker` | `AtFullSide.K1.HeadAtBaseMaker` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K1.linksW` | `AtFullSide.K1.LaysAtSwitches` | yes | propext |
| `ProofFile.Honest.K12.AtFile.LotWJoint.samples_of_shape` | `Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointSamplesAtShape` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_whole` | `Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAcceptedWhole` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K13.wDataAt_ready_heard` | `Johnson.Desc.ProofFile.Honest.K13.DefaultsIdle` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K13.wData_ready_own` | `Johnson.Desc.ProofFile.Honest.K13.DefaultsIdle` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.linOk_at_head` | `Johnson.Desc.ProofFile.Honest.K14.SendingsAtFilling` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.mask_no_tail` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.mask_one_place` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.messages_apart` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Quot.sound |
| `ProofFile.Honest.K14.one_coin_turns` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.plan_below` | `Johnson.Desc.ProofFile.Honest.K14.SendingsPlan` | yes | propext, Quot.sound |
| `ProofFile.Honest.K14.plan_last_all` | `Johnson.Desc.ProofFile.Honest.K14.SendingsPlan` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.plan_rows_high` | `Johnson.Desc.ProofFile.Honest.K14.SendingsPlan` | yes | propext, Quot.sound |
| `ProofFile.Honest.K14.publicIdle_at_head` | `Johnson.Desc.ProofFile.Honest.K14.DefaultsIdleAtHead` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.sendings_at_head` | `Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.sent_within_coins` | `Johnson.Desc.ProofFile.Honest.K14.SendingsWithin` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_all` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_apart` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_once` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_reads` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Quot.sound |
| `ProofFile.Honest.K14.spot_share` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_sum` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.spot_zero` | `Johnson.Desc.ProofFile.Honest.K14.SendingsReach` | yes | propext, Quot.sound |
| `ProofFile.Honest.K14.trees_at_head` | `Johnson.Desc.ProofFile.Honest.K14.WidthAllTrees` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K14.width_all_head` | `Johnson.Desc.ProofFile.Honest.K14.WidthAllTrees` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K5.ground_at_head` | `Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.K9.SeatedClose.stepS` | `Johnson.Desc.ProofFile.Honest.K9.CloseYes` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.thread_in_first` | `Johnson.Desc.ProofFile.Honest.Law.InsideFile` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.thread_in_second` | `Johnson.Desc.ProofFile.Honest.Law.InsideFile` | yes | propext, Classical.choice, Quot.sound |
| `ProofFile.Honest.thread_in_shared` | `Johnson.Desc.ProofFile.Honest.Law.InsideFile` | yes | propext, Classical.choice, Quot.sound |
| `Rom.binding_overOne` | `Rom.ExitBind` | yes | propext, Classical.choice, Quot.sound |
| `Run.CostP.laxWhole` | `Run.CostLax` | yes | propext, Quot.sound |
| `Run.CostP.parseFullW` | `Run.CostFull` | yes | propext, Classical.choice, Quot.sound |
| `Run.CostP.wholeChain` | `Run.CostFmtProofs` | yes | propext, Classical.choice, Quot.sound |
| `ShapeLines.last_run_at_border358` | `ShapeLines.LastChain.LastRunAtBorder358` | yes | propext, Quot.sound |
| `TopC.bfV_lower` | `ZKCP.HonestKeyVerBf` | yes | propext, Classical.choice, Quot.sound |
| `TopC.bfV_qb` | `ZKCP.HonestKeyVerBf` | yes | propext, Classical.choice, Quot.sound |
| `TopC.bf_E` | `ZKCP.HonestKeyVerBf` | yes | propext, Classical.choice, Quot.sound |
| `TopC.bf_W` | `ZKCP.HonestKeyVerBf` | yes | propext, Classical.choice, Quot.sound |
| `TopC.target_fit_iff` | `Cond.ObjBounds` | yes | propext, Classical.choice, Quot.sound |
| `TwRound.lb_entN` | `Johnson.Desc.First.Look.K3CallerErr` | yes | propext, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.bindingGAt` | `Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.bindingR_one` | `Johnson.TypedOracleCompiler.RecCompile.FrontRoot` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.cmsA_bcs` | `Johnson.TypedOracleCompiler.RecCompile.CmsAns` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.cmsA_binding_at` | `Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.cmsRA_binding_at` | `Johnson.TypedOracleCompiler.RecCompile.FrontRootAns` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.coreA` | `Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.detBound_VRA` | `Johnson.TypedOracleCompiler.RecCompile.FrontRootAns` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.pr_step4_le` | `Johnson.TypedOracleCompiler.RecCompile.Seeds` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.Cms.pub_lift` | `Johnson.TypedOracleCompiler.RecCompile.PublicLift` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.hashEvents` | `OnBytes.TypedOracleCompiler.Compile.Batch.Hash` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.pr_stepS_le` | `OnBytes.TypedOracleCompiler.Compile.Batch.Sound` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.stOf_full` | `OnBytes.TypedOracleCompiler.Compile.Batch.Sound` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.stOf_prover` | `OnBytes.TypedOracleCompiler.Compile.Batch.Sound` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.stOf_start` | `OnBytes.TypedOracleCompiler.Compile.Batch.Sound` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Compile.Batch.stOf_ver` | `OnBytes.TypedOracleCompiler.Compile.Batch.Sound` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Iop.RoundsQueryLayout.clearedIsUniformOnPassing` | `Hiop.SoundAsIOPClearing` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Joined.proofSound_plainJB` | `Johnson.Desc.Plain.BothAtDesc` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Joined.sndBKT_of_links` | `OnBytes.TypedOracleCompiler.Joined.LinkJ` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Slice.full_one_world` | `OnBytes.TypedOracleCompiler.Slice.EntryFullTop` | yes | propext, Classical.choice, Quot.sound |
| `TypedOracleCompiler.Slice.small_one_world` | `OnBytes.TypedOracleCompiler.Slice.EntrySmallTop` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.ArgumentSystem.run_verify` | `VerifiableInference.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.Label` | `VerifiableInference.RequestLabel` | yes | none |
| `VerifiableInference.AtEveryRequest.Outcome` | `VerifiableInference.AtEveryRequest` | yes | none |
| `VerifiableInference.AtEveryRequest.ProofAcceptedWhere` | `VerifiableInference.AtEveryRequest` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.Simulator` | `VerifiableInference.AtEveryRequest` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.WellFormedRequest` | `VerifiableInference.WellFormedRequests` | yes | none |
| `VerifiableInference.AtEveryRequest.WithinBudget` | `VerifiableInference.AtEveryRequest` | yes | none |
| `VerifiableInference.AtEveryRequest.ZeroKnowledgeBelowWhere` | `VerifiableInference.AtEveryRequest` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.ZeroKnowledgeShownBelowWhere` | `VerifiableInference.Labelled` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.ZeroKnowledgeWhere` | `VerifiableInference.AtEveryRequest` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.bitOf_requestLabel` | `VerifiableInference.RequestLabel` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.modelResult` | `VerifiableInference.WellFormedRequests` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.proofAcceptedWhere_iff` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.requestLabel` | `VerifiableInference.RequestLabel` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.requestLabel_eq_failed_iff` | `VerifiableInference.RequestLabel` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.requestLabel_eq_otherTokens_iff` | `VerifiableInference.RequestLabel` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.requestLabel_eq_served_iff` | `VerifiableInference.RequestLabel` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.requestOutcome` | `VerifiableInference.RequestOutcome` | yes | propext, Quot.sound |
| `VerifiableInference.AtEveryRequest.served_iff_canServe` | `VerifiableInference.AtEveryRequestGuards` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.simulatedExperiment` | `VerifiableInference.AtEveryRequest` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.toldWeightsSaysNothing` | `VerifiableInference.AtEveryRequestGuards` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.wellFormed_and_result_iff` | `VerifiableInference.WellFormedRequests` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.AtEveryRequest.zeroKnowledgeFollowsFromOn` | `VerifiableInference.AtEveryRequestFollows` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.BindsWith.extractsDrawn` | `Johnson.Bind.ExtractsDrawn` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.BindsWith.mono` | `VerifiableInference.Binds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.BindsWith.noTwoOpenings` | `VerifiableInference.NoTwoOpenings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.constantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.exampleLayerSettings` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | none |
| `VerifiableInference.Bounds.exampleSettings` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext |
| `VerifiableInference.Bounds.exists_passesWorstCaseCheck` | `VerifiableInference.Bounds.SomeWeightsPassAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.greedyOutput_countingModelWeights` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.layerWithin_mediumConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.markingWeightsAt_small` | `VerifiableInference.Bounds.MarkingWeightsAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.mediumConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNeverFails_constantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNeverFails_of_small_entries` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNextToken_countingModelWeights` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNextToken_countingModelWeights_apart` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNextToken_markingModelWeights_apart` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.modelNextToken_markingWeightsAt_apart` | `VerifiableInference.Bounds.MarkingWeightsAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.not_allConditionsHold_largeConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsDoNotPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.not_modelNeverFails_largeConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsDoNotPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.not_passesLeastBoundWorstCaseCheck_largeConstantModelWeights` | `VerifiableInference.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.not_passesLengthWorstCaseCheck_largeConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.not_passesWorstCaseCheck_largeConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsDoNotPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLeastBoundCheck_mediumConstantModelWeights` | `VerifiableInference.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLeastBoundCheck_of_passesFrobeniusLengthCheck` | `VerifiableInference.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLeastBoundCheck_of_small_entries` | `VerifiableInference.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLengthCheck_mediumConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLengthCheck_of_small_entries` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesFrobeniusLengthCheck_of_uniformLengthCheck` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesLeastBoundWorstCaseCheck_of_passesLengthWorstCaseCheck` | `VerifiableInference.Bounds.LeastBoundOfLength` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesLengthWorstCaseCheck_of_uniformLengthCheck` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_constantModelWeights` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_countingModelWeights` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_markingModelWeights` | `VerifiableInference.Bounds.PassingWeightsTellPromptsApart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_of_small_entries` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_of_uniformCheck` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.passesWorstCaseCheck_of_zero_layers` | `VerifiableInference.Bounds.SomeWeightsPassAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.requestResult_largeConstantModelWeights` | `VerifiableInference.Bounds.SomeWeightsDoNotPass` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.uniformCheck_exampleSettings` | `VerifiableInference.Bounds.SomeWeightsPass` | yes | propext, Quot.sound |
| `VerifiableInference.Bounds.uniformCheck_zero_of_settingsAreValid` | `VerifiableInference.Bounds.SomeWeightsPassAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Bounds.uniformLengthCheck_exampleSettings` | `VerifiableInference.Bounds.SomeWeightsPassLengthCheck` | yes | propext, Quot.sound |
| `VerifiableInference.Bounds.weightsAreValid_markingWeights_of_settingsAreValid` | `VerifiableInference.Bounds.MarkingWeightsAtValidSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.CanServe` | `VerifiableInference.CanServe` | yes | propext, Quot.sound |
| `VerifiableInference.Commitment` | `VerifiableInference.Statements` | yes | none |
| `VerifiableInference.Compilation.BindingOf` | `Johnson.Face.FinalBindingStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.CompleteAtFiles` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.CompleteIOP` | `Johnson.Face.CompleteAsIOP` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.CompleteInParts` | `Johnson.Face.CompleteAsIOP` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.ExactOutsideStops` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FilesInUse` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FilesTaken` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalComplete` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalHandsOutNoProof` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalRefusedHandsOutNoProof` | `Johnson.Face.FinalStatementOneBit` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalSound` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalSoundAndBinding` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalStatement` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalStatementOneBit` | `Johnson.Face.FinalStatementOneBit` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalStatementOneBit.mk` | `Johnson.Face.FinalStatementOneBit` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalZeroKnowledge` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.FinalZeroKnowledgeOneBit` | `Johnson.Face.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.HonestProvers.refuseUnserved` | `Johnson.Face.Protocol` | yes | propext, Quot.sound |
| `VerifiableInference.Compilation.HonestProversAndSettingsAtFiles` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.HonestVerifierZeroKnowledge` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.PrivateStopsAtMost` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.RepliesFit` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.RepliesFitAtFiles` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.RunByRun` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.RunSimulators` | `Johnson.Face.Protocol` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.Spec.compiled_indexPrivacy` | `VerifiableInference.Final.CompilerTheorems` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.TableBudgetFits` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.WholeLife` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.ZeroKnowledgeOnServedRequests` | `VerifiableInference.Final.ZeroKnowledgeAtTheProtocol` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.at_all_files_in_use_some_weights_pass` | `AtFullSide.E2E.TheWorstCaseCheckCanBeMet` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.beneath_at` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.beneath_at_T1` | `AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.beneath_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.bindingOf_value` | `AtFullSide.Face.FinalBindingAtTheValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.bitsBinding_le_finalBindingError` | `Johnson.Face.FinalBindingProof` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.bothEnds_in_scope` | `AtFullSide.E2E.BothEndsAtOneTerm` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.budgetAtFiles` | `VerifiableInference.Final.CompilerPublicAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.commitmentLife` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | none |
| `VerifiableInference.Compilation.compile` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_eq_slotSystemF` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_flashProve_sound_iff` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_flashProve_verify` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_flashProve_verify_eq` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_sound_iff` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compile_verify` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiledSide` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiledVerifier_eq_verify` | `Johnson.Face.Compiler` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiled_complete_atEveryCoin_holds` | `VerifiableInference.Final.CompilerComplete` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiled_complete_holds` | `VerifiableInference.Final.CompilerComplete` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiled_indexPrivacy` | `Johnson.T3.CompiledPrivacy` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiled_protocol_is_the_bound` | `AtFullSide.CompletenessAndZeroKnowledge.ThreeAtFilesOfEnds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.compiled_provers_are_the_triple` | `AtFullSide.CompletenessAndZeroKnowledge.ThreeAtFilesOfEnds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.completeOnServedRequests_at_every_files_in_use` | `AtFullSide.E2E.CompleteAtEveryFilesInUse` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.completeOnServedRequests_refuse_iff` | `VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_own_outputs` | `AtFullSide.E2E.CompleteAtEveryPrompt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_the_stored_files_at_small_weights` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtSmallWeights` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_the_stored_files_at_the_constant_weights` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtSmallWeights` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_the_stored_files_at_the_marking_weights` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_the_stored_files_at_the_weights_of_800` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsWithin800` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.complete_at_the_stored_files_at_weights_within_800` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsWithin800` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.err_commitmentLife` | `Johnson.T3.WholeViewFollows` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.everyRequest` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Quot.sound |
| `VerifiableInference.Compilation.filesInUse_stored` | `AtFullSide.CompletenessAndZeroKnowledge.LinesAtStoredFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalAtT1_filled` | `AtFullSide.E2E.TheCompiledStepFilled` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalAtT1_filled_withRoom` | `AtFullSide.E2E.TheCompiledStepFilled` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalBindingError` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalCompleteAtEveryPrompt_of_finalComplete` | `AtFullSide.E2E.CompleteAtEveryPrompt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalCompleteAtEveryRequest_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalComplete_iff_completeOn` | `Johnson.Face.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalComplete_value` | `AtFullSide.Face.FinalCompleteValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalExtractor` | `Johnson.Face.FinalBindingStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalExtracts_value` | `AtFullSide.Face.FinalBindingAtTheValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalHandsOutNoProof_of_refused` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalHandsOutNoProof_value` | `AtFullSide.Face.HonestProversAndSettingsValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalOpeningError` | `Johnson.Face.FinalBindingStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalRefusedHandsOutNoProof_value` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSound` | `Johnson.Face.FinalSoundProof` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSoundAndBinding_value` | `AtFullSide.Face.FinalBindingAtTheValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSoundOpened_value` | `AtFullSide.Face.FinalBindingAtTheValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSoundnessError_le_finalBindingError` | `Johnson.Face.FinalSoundAtExtractor` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalStatement_of_oneBit` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSystem` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalSystem_verifier_at_blake2b` | `Johnson.Face.ExecutableVerifier` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalVerifier_eq` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledgeAtEveryRequest_of_oneBit` | `Johnson.Face.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledgeAtEveryRequest_of_oneBit_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledgeError` | `AtFullSide.Face.ZeroKnowledgeNumber` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledgeOneBit_at` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledgeOneBit_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledge_of_atEveryRequest` | `Johnson.Face.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledge_of_oneBit` | `Johnson.Face.FinalStatementOneBit` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.finalZeroKnowledge_of_oneBit_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.final_of_the_two_holds` | `Johnson.CompletenessAndZeroKnowledge.FinalRoadProof` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.flashProveAtFiles` | `Johnson.Face.FinalStatement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.handsOutNoProof_of_honestPartOf` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.handsOutNoProof_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.honestProversAndSettings` | `AtFullSide.Face.HonestProversAndSettingsValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.honestProversAndSettingsOf` | `AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.honestProvers_arm` | `Johnson.CompletenessAndZeroKnowledge.SendsAtTerm` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.life_err_at_zero_zero` | `AtFullSide.CompletenessAndZeroKnowledge.LifeNumberAt135` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.life_number_at_most` | `AtFullSide.CompletenessAndZeroKnowledge.LifeNumberAt135` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.noProofForm` | `Johnson.Face.FinalStatement` | yes | none |
| `VerifiableInference.Compilation.passesSomeWorstCaseCheck_of_settings_eq` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsWithin800` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.proversAtFiles` | `VerifiableInference.Final.ZeroKnowledgeAtTheProtocol` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.realSide` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.rejectsNoProof_flashProve` | `AtFullSide.CompletenessAndZeroKnowledge.RejectsTheEmptyForm` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.rejectsNoProof_value` | `AtFullSide.CompletenessAndZeroKnowledge.RejectsTheEmptyForm` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.repliesFit_value` | `AtFullSide.Face.HonestProversAndSettingsValue` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.requestLabel_ne_failed_where_some_worst_case_check_passes` | `AtFullSide.E2E.CompleteWhereSomeWorstCaseCheckPasses` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.requestLabel_ne_failed_where_the_worst_case_check_passes` | `AtFullSide.E2E.CompleteWhereTheWorstCaseCheckPasses` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.secondArm_at_the_stored_files` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsWithin800` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.served_at_T1` | `AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.simulatedRuns` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.simulatorsByTable` | `VerifiableInference.Final.ZeroKnowledgeBeforeHashing` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.someRequestIsServedInUse` | `Johnson.Face.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.someRequestIsServed_holds` | `VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.someWeightsPassAtAllValidSettings` | `AtFullSide.E2E.TheWorstCaseCheckCanBeMet` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.some_weights_pass_at_all_files_in_use` | `AtFullSide.E2E.TheWorstCaseCheckCanBeMet` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.statementAtStoredFiles_holds` | `AtFullSide.Face.TheFinalStatementHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.stepErrorAtTheStops` | `AtFullSide.E2E.TheCompiledStepFilled` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.stepError_below_bar` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.stops_below_bar` | `AtFullSide.Face.ZeroKnowledgeNumber` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.stops_number_154` | `AtFullSide.CompletenessAndZeroKnowledge.StopsNumberAt154` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.storedMarkingWeights_pass` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.storedMarkingWeights_read_an_earlier_token` | `AtFullSide.E2E.CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.termLeft_at` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.termLeft_of_ends` | `AtFullSide.CompletenessAndZeroKnowledge.LinesAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.termLeft_value` | `AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementBothHold` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementHolds` | `AtFullSide.Face.TheFinalStatementHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementHolds_at` | `AtFullSide.Face.TheFinalStatementHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementOneBitAlone` | `AtFullSide.Face.TheFinalStatementOneBitAlone` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementOneBitHolds` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theFinalStatementOneBitHolds_at` | `AtFullSide.Face.TheFinalStatementOneBitHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theHonestPart_completeAtEveryPrompt` | `AtFullSide.E2E.CompleteAtEveryPrompt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theHonestPart_complete_where_rangeConditionsNeverFail` | `AtFullSide.E2E.CompleteAtEveryPrompt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes` | `AtFullSide.E2E.CompleteWhereSomeWorstCaseCheckPasses` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theHonestPart_complete_where_the_worst_case_check_passes` | `AtFullSide.E2E.CompleteWhereTheWorstCaseCheckPasses` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theProvers` | `Johnson.Face.HonestProversWithCompiledPart` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theProvers_eq` | `Johnson.CompletenessAndZeroKnowledge.TheProversEq` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.theSettings` | `Johnson.CompletenessAndZeroKnowledge.TheSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.threeAtFiles_in_use` | `AtFullSide.Face.TheThreeAtTheFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.threeAtFiles_of_ends` | `AtFullSide.CompletenessAndZeroKnowledge.ThreeAtFilesOfEnds` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.verdictOf_eq_finalVerifierProgram` | `Johnson.Face.ExecutableVerifier` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.verify_rejects_noProofForm` | `AtFullSide.CompletenessAndZeroKnowledge.RejectsTheEmptyForm` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.zkOnServedRequests_atTheStoredFiles` | `AtFullSide.E2E.ZeroKnowledgeFromTheRowsAtTheStoredFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Compilation.zkOnServedRequests_inScope` | `AtFullSide.E2E.ZeroKnowledgeFromTheRows` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.First.Att.P.K05_law_one_guard` | `Johnson.Desc.First.Att.K05LawGuard` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.First.K2Caller.k2_err_cap` | `Johnson.Top.H0.K2Caller.CapAt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.First.K8.k08_piece_at_maker` | `Johnson.Desc.First.K8.PieceEq` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.First.MergeLaw.merge_goodIn_cap` | `Johnson.Top.H0.MergeLaw.AtSeat` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.K9L.num_k9` | `Johnson.Desc.First.Batch.Law.AtCap` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Key.PinsStay.onAt` | `Johnson.Desc.Key.KeyPinsRide` | yes | propext, Quot.sound |
| `VerifiableInference.Desc.Kinds.Head.Law.Bears.k06BearsCap` | `Johnson.Desc.Kinds.Law.K06Bears` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Kinds.Head.Law.Came.k7_own` | `Johnson.Desc.Kinds.Law.K7Tied` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_guard` | `Johnson.Desc.Kinds.Law.HeadCutsFive` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Last.shapeAt_zero_iff` | `Johnson.Desc.Last.ShapeDoor` | yes | propext, Quot.sound |
| `VerifiableInference.Desc.Last.step_two` | `Johnson.Desc.Last.ShapeGives` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Plain.fold_chain` | `Johnson.Desc.Plain.FoldChain` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Sound.chainOfPromisesR` | `Johnson.Desc.Sound.ChainOfPromisesR` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Desc.Sound.eachLawsBNOwn_plain` | `Johnson.Desc.Sound.SharedJointCountLedgerOwn` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Meaning.meaning_atFiles` | `Johnson.Goal.Meaning.NextToken` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Meaning.meaning_nextToken` | `Johnson.Goal.Meaning.NextToken` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.CompilerSoundnessConditions.binds` | `Johnson.Top.InnerCompiledVerifier` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.Spec.indexKnowledgeSoundIOP_iff_premises` | `Johnson.Top.SoundAsIOPIsThePremise` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.entrySoundOfFullD_of_joh` | `Johnson.Flat.Dec.EntryAtGate` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.indexKnowledgeSoundIOP_iff_premises` | `Johnson.Top.SoundAsIOPIsThePremise` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.innerCompiledVerifier_eq` | `Johnson.Top.InnerCompiledVerifierSide` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound` | `Johnson.Top.InnerCompiledVerifier` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.innerCompiledVerifier_soundFor` | `Johnson.Top.InnerCompiledVerifier` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.innerCompiledVerifier_soundFor_byPublicReading` | `Johnson.Top.InnerCompiledVerifierByPublicReading` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.rows_at_descB` | `Johnson.Goal.Skeleton.ProofRowsAtDesc` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.seedLaw_fullD` | `Johnson.Flat.Dec.ElevenAt` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.tie_of_some` | `Johnson.Goal.Meaning.TieAtSome` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.told_bindsWith_on` | `Johnson.Top.OpensTold` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.told_binds_core` | `Johnson.Top.InnerCompiledVerifierByPublicReading` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.told_binds_written` | `Johnson.Goal.Conditions.BindsLaw` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.OnPublicFiles.verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor` | `Johnson.Top.InnerCompiledVerifierByPublicReading` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PassesLeastBoundWorstCaseCheck` | `VerifiableInference.Bounds.LeastBoundNeverFails` | yes | propext, Quot.sound |
| `VerifiableInference.PassesSomeWorstCaseCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Quot.sound |
| `VerifiableInference.PassesWorstCaseCheck` | `VerifiableInference.Bounds.NeverFails` | yes | propext, Quot.sound |
| `VerifiableInference.PlanWritten.cut_of_row` | `Johnson.Desc.Ok.PlanWritten.CutTestLaws` | yes | propext |
| `VerifiableInference.PublicSetup` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.casesOn` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.ctorIdx` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.files` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.inUse` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.mk` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.mk.inj` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.mk.injEq` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.mk.noConfusion` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.mk.sizeOf_spec` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.noConfusion` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.noConfusionType` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.readParameters` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.rec` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.PublicSetup.recOn` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.Rec.soundForWith_systemE` | `Johnson.Top.FrontEnc` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.RequestForm` | `VerifiableInference.RequestResult` | yes | none |
| `VerifiableInference.SoundForWith.bindWeights` | `Johnson.PV.FitO` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.SoundForWith.soundAfterHonestCommitmentFor` | `VerifiableInference.AgreementWith` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.acceptAll_complete` | `VerifiableInference.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_and_modelOutput_iff` | `IntegerModel.Arrays.RequestResultLaws` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_exists` | `VerifiableInference.ModelGuards` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_iff` | `IntegerModel.Arrays.SameModel` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_iff_of_passesSomeWorstCaseCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_iff_of_passesWorstCaseCheck` | `VerifiableInference.Bounds.NeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_iff_of_rangeConditionsNeverFail` | `VerifiableInference.CanServeWhereNoConditionFails` | yes | propext, Quot.sound |
| `VerifiableInference.canServe_iff_requestResult` | `VerifiableInference.RequestResult` | yes | propext, Quot.sound |
| `VerifiableInference.canServe_nowhere_atHaltingWeights` | `VerifiableInference.ModelGuardsAtReference` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.canServe_of_modelNeverFails` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Quot.sound |
| `VerifiableInference.canServe_weightsOfIndex_iff` | `IntegerModel.Arrays.SameModel` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.completeAtWellFormedRequests` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.completeOnCanServe` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.completeOn_of_public` | `Johnson.Goal.Conditions.CompleteOfPublic` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.completeWhereSomeWorstCaseCheckPasses` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.completeWhereTheWorstCaseCheckPasses` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.complete_stored` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.exists_greedyOutput` | `VerifiableInference.GreedyOutputExists` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.exists_greedyOutput_of_length` | `VerifiableInference.GreedyOutputExists` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.flashProve` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.greedyOutput_unique` | `VerifiableInference.GreedyOutputExists` | yes | propext, Quot.sound |
| `VerifiableInference.labelled` | `VerifiableInference.Labelled` | yes | none |
| `VerifiableInference.lawful_scalesOf` | `IntegerModel.Arrays.OfIndex` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.leanVerifier` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.leanVerifier_eq` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.markedEntry_referenceSettings` | `VerifiableInference.Bounds.TheMarkAtReferenceSettings` | yes | propext, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesFrobeniusLeastBoundCheck` | `VerifiableInference.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesFrobeniusLengthCheck` | `VerifiableInference.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesGramTest` | `VerifiableInference.Bounds.GramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesLeastBoundScaledGramTest` | `VerifiableInference.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesLeastBoundWorstCaseCheck` | `VerifiableInference.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesLengthWorstCaseCheck` | `VerifiableInference.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesScaledGramTest` | `VerifiableInference.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesSmallerSideGramTest` | `VerifiableInference.Bounds.SmallerSideGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesSomeWorstCaseCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_passesWorstCaseCheck` | `VerifiableInference.Bounds.NeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.modelNeverFails_of_rangeConditionsNeverFail` | `VerifiableInference.ModelNeverFails` | yes | propext, Quot.sound |
| `VerifiableInference.modelNextToken_eq_nextToken` | `IntegerModel.Arrays.SameModel` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.not_complete_of_rejected` | `VerifiableInference.NotComplete` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.not_modelNeverFails_atHaltingWeights` | `VerifiableInference.TheModelsOwnOutputCanFail` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.not_passesWorstCaseCheck_atHaltingWeights` | `VerifiableInference.Bounds.TheCheckCanFail` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.not_rangeConditionsNeverFail_atHaltingWeights` | `VerifiableInference.TheModelsOwnOutputCanFail` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.not_theModelsOwnOutputExists_atHaltingWeights` | `VerifiableInference.TheModelsOwnOutputCanFail` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.onlineRunsPerCopy` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.own_output_of_result` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesFrobeniusLengthCheck_atReferenceSettings` | `VerifiableInference.Bounds.PassLengthCheckAtReferenceSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesSomeWorstCaseCheck_atReferenceSettings` | `VerifiableInference.Bounds.PassLengthCheckAtReferenceSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesSomeWorstCaseCheck_of_passesFrobeniusLeastBoundCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesSomeWorstCaseCheck_of_passesLeastBoundScaledGramTest` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesSomeWorstCaseCheck_of_passesLengthWorstCaseCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.passesWorstCaseCheck_atReferenceSettings` | `VerifiableInference.Bounds.PassAtReferenceSettings` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesGramTest` | `VerifiableInference.Bounds.GramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck` | `VerifiableInference.Bounds.LeastBoundNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesLengthWorstCaseCheck` | `VerifiableInference.Bounds.LengthNeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesScaledGramTest` | `VerifiableInference.Bounds.ScaledGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesSmallerSideGramTest` | `VerifiableInference.Bounds.SmallerSideGramTestOfStretchNumbers` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesSomeWorstCaseCheck` | `VerifiableInference.Bounds.SomeWorstCaseCheck` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rangeConditionsNeverFail_of_passesWorstCaseCheck` | `VerifiableInference.Bounds.NeverFails` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.realExperiment` | `VerifiableInference.Statements` | yes | none |
| `VerifiableInference.referenceSettings_valid` | `VerifiableInference.ModelGuardsAtReference` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.refusedHandsOutNoProof` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rejectAll_sound` | `VerifiableInference.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.rejectsEmptyProof` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.repliesFit` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.reply` | `VerifiableInference.Labelled` | yes | none |
| `VerifiableInference.requestForm_iff_requestOfTokens` | `IntegerModel.Arrays.RequestResultLaws` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.requestLabel_ne_failed` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Quot.sound |
| `VerifiableInference.result_of_own_output` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.settingsOf_scalesOf` | `IntegerModel.Arrays.OfIndex` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.sound` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.soundAndBinding` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.soundAndBinding_stored` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.soundForWith_via` | `Johnson.Top.SoundVia` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.soundOpened_of_soundAndBinding` | `VerifiableInference.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.sound_iff` | `VerifiableInference.Agreement` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.sound_of_soundAndBinding` | `VerifiableInference.Checks` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.sound_stored` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.storedSetup` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.theModelsOwnOutputExists_of_rangeConditionsNeverFail` | `VerifiableInference.TheModelsOwnOutputFromRangeConditions` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.theModelsOwnOutput_unique` | `VerifiableInference.TheModelsOwnOutput` | yes | propext, Quot.sound |
| `VerifiableInference.validSettings_exist` | `VerifiableInference.ModelGuards` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeAtEveryRequest` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeAtEveryRequest_of_lines` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeBelow_of_onCanServe` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeOnCanServe` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeWithLabel` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledgeWithLabel_of_atEveryRequest` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifiableInference.zeroKnowledge_stored` | `AtFullSide.Face.TheSixLines` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtFiles.every_output_at_meets_iff` | `Johnson.Goal.Files.MeetsPolicyAtFiles` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.carries` | `Johnson.Goal.Conditions.RowsAtTheRecord` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.count_the` | `Johnson.Goal.Conditions.RowsAtTheRecord` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.errorAtBits` | `Johnson.Goal.Conditions.RowsAtTheRecord` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.hext` | `Johnson.Goal.TopOfThree` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.indexBindingUnderPolicy_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.indexBindingWith_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.indexBinding_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.keySound_at_live_holds` | `Johnson.Goal.Conditions.KeyOpenHolds` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.kindsLaws_at_head` | `Johnson.Goal.Skeleton.KindsLawsAtHead` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.meaning` | `Johnson.Goal.TopOfThree` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.nearestSound_of_verify` | `Johnson.Goal.Skeleton.SoundOfVerifyAt` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.noTwoAnswers_of_verify_at` | `Johnson.Goal.Skeleton.NoTwoAnswersOfVerify` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.proofSoundAt_of_verify` | `Johnson.Goal.Skeleton.SoundOfVerifyMore` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.proofSound_of_rows` | `Johnson.Goal.Skeleton.ProofFile` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.read_of_scope` | `Johnson.Goal.Skeleton.SoundOfVerifyGoals` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.relationMeans` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.sessionAugmented_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.sessionAugmented_union_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyMore` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundForGaps_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyGaps` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundManyProofs_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundManyProofs_union_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyForms` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundOpened_level_digits_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyMore` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_numbers` | `Johnson.Goal.Skeleton.TopAtZ` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.soundUnderPolicy_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyPolicy` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.sound_of_verify_at` | `Johnson.Goal.Skeleton.SoundOfVerifyAt` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.sound_of_verify_at_through_the_IOP` | `E2E.SoundAsIOPAtFilesProofs` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.AtTheName.sound_of_verify_parsers_at` | `Johnson.Goal.Skeleton.SoundOfVerifyMore` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.Fit.BindsWith.min_one` | `Ladder.FitBindsBits` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.Fit.epsBind_min_le_bitsBinding` | `Ladder.FitBindsBits` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.Fit.soundForWith_system_of_toldO` | `Johnson.PV.FitO` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.InScope` | `Ladder` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.completeOn_iff_proofAccepted` | `Ladder.Ties` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.filesRead` | `Johnson.Goal.Files.FilesReadProof` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.frame_le_bits` | `Ladder.BitsOfStep` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.inScope_zAt` | `Johnson.Goal.Files.ScopeAtPolicies` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.readFiles` | `Ladder` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.settingsOfRead_full` | `Johnson.Goal.Files.FilesReadAtRef` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.settingsOfRead_gap` | `Johnson.Goal.Files.FilesReadAtRef` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.storedPublicFiles` | `Ladder.Stored` | yes | propext |
| `VerifierAndGoals.theDescription_eq` | `Johnson.Goal.Description.Description` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.theDescription_out` | `Johnson.Goal.Description.Description` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.theDescription_within` | `Johnson.Goal.Description.Description` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.valid_of_read` | `Ladder.Ties` | yes | propext, Classical.choice, Quot.sound |
| `VerifierAndGoals.verify` | `Ladder` | yes | propext, Classical.choice, Quot.sound |
| `ZKCP.HasIndexBindingWith.digestKey` | `Compile.DigestKeyBinding` | yes | propext, Classical.choice, Quot.sound |
| `ZKCP.refined_of_perfect` | `ZKCP.RefinedOfPerfect` | yes | propext, Classical.choice, Quot.sound |
| `ZKCP.toy_refined` | `ZKCP.Sanity` | yes | propext, Classical.choice, Quot.sound |

The audit's two verdicts in the full check's run, in its own words:

- "axioms PASSED: every declaration that Lean attributes to a module of the library was checked: all 592112 declarations in all 29549 modules, and all 9883 copies of theorems that stand in more than one module (Lean keeps one of each; every copy is walked from its own module's file), depend on no axiom but propext, Classical.choice and Quot.sound"
- "kinds PASSED: no declaration of ours is an axiom, opaque, unsafe or partial, or has implemented_by or extern; no module of ours has a csimp entry, or an entry in [Lean.regularInitAttr, Lean.builtinInitAttr], or is of the module system; all 4217 constants with the last name part _unsafe_rec are as Lean's own. EXCEPT, and not counted: 4217 declarations foo._unsafe_rec, which ARE marked partial: Lean makes one, for its compiler, beside every definition by recursion, and the kernel lets no safe declaration speak of it"

The audit gives no verdict on the form of any named statement: every line of `scripts/top-theorems.txt` is of the kind "general". The 13 files under `Ask/` belong to no library and are outside the audit. Without a verdict it reports 78 statements with `Spec` in their names that no theorem of the library concludes unless it has a hypothesis so named.

The independent checker (nanoda: [CHECKING.md](CHECKING.md), "The independent checker"). Over a copy of the compiled files of the build in seven calls told above (that the compiled files it read were that build's is known from a report alone) it has accepted the soundness theorem on `verify` (`VerifierAndGoals.AtTheName.sound_of_verify_at`), with every declaration beneath it, and nothing that does not lie beneath it, in a pass on that theorem's export alone. That run's own lines: "ASKED: VerifierAndGoals.AtTheName.sound_of_verify_at"; "TEXT: 207461 declarations ; …"; "RECOUNT: 207461"; "READ BACK: 207461 of 207461 agree"; "AXIOMS IN THE TEXT: propext, Quot.sound, Classical.choice"; "TAKEN AS AXIOMS BY THE CHECKER: 0"; "Checked 207461 declarations with no errors"; "NANODA: exit 0 ; stderr 0 bytes". The line "Checked …" is the public program `nanoda_bin`'s; the others are those of this project's own programs, whose exporter wrote the text out of the compiled files; they were gathered into one print after the run, from the run's own files. The print names the files of that copy by a list of their checksums, not by the checksum above: the copy held no file of `scripts/`; the Lean files and the Lake files were this repository's; the compiled files of Mathlib and the other packages were that machine's own copy, the same by checksum as the build's; Lean's own files on that machine were not held by checksums. That the exporter read that copy's compiled files for the modules which the theorem's module imports, and not for that module alone, rests on a reading of the scripts that ran it. Of the six theorems ([CHECKING.md](CHECKING.md), "The six theorems, and eight more") the independent checker has accepted `sound`, `repliesFit` and `refusedHandsOutNoProof` by name, over a build of this repository's files; over such a build the three on binding, completeness and zero knowledge have been checked by Lean's kernel alone. Each of these passes was on that theorem's export alone, over a copy of the same compiled files (that the compiled files that these passes read were that build's is known from a report alone; Lean's own files were not compared with a list of checksums), and what is told above of the first pass's print, packages and exporter holds of it too: `VerifiableInference.sound` ("Checked 212320 declarations with no errors"); `VerifiableInference.repliesFit` ("Checked 53441 declarations with no errors"); `VerifiableInference.refusedHandsOutNoProof` ("Checked 50871 declarations with no errors"). In one pass more, on that theorem's export alone, it has accepted `VerifiableInference.soundAndBinding` ("Checked 213394 declarations with no errors"), with every declaration beneath it. That pass was made over a copy of the compiled files of another build, of Lean files that differ from this repository's. The text that was put to the checker is, by checksum, the one that the exporter writes over a copy of the compiled files of the build in seven calls told above; the pass was not made over that copy itself.

The Lean verifier's reference run. Of the reference run 109 calls of the command `lean-verify` are told first. The calls load compiled Lean files made beforehand; the library's own compiled files, the command and the parser are held by checksums before and after the calls, and every file of the command and of the parser outside `lean/` that the traced calls beside them opened has this repository's checksum (none of the run's own calls was traced: [GAPS.md](GAPS.md), 14, "Which programs (k)"). That the library's compiled files are made from this repository's Lean files is Lake's finding at the build in seven calls told above, not the run's; that the command and the parser read these files and no others is not shown. In these 109 calls all 47 proofs labelled honest are accepted (45 at exact match, 2 under a tolerant policy). None of the 57 labelled lying and none of the 5 controls (honest proofs beside a claim that is not theirs) is: 54 of the 57 and the 5 are rejected, and 3 end at the parser, with no verdict. The labels are the files' own. The proofs are not made in the run, and 42 of the 47 come from a prover built from other sources than this repository's; the weights are synthetic; no lying proof is under a tolerant policy; the program `cp_verify` is not run; all calls run on one machine; of the proof files only the two stored examples are in this repository. All 109 calls end as written down beforehand. Nine further calls of the run, on the small stored example beside altered parameter files, all end at the parser, with no verdict, as written down beforehand. Beside them the public test's command for the stored full-size example was run once apart from the test runner, on the same machine: exit status 0, "VERDICT: ACCEPT (exact match)". In the same run the command is called on a second set of 41 proofs labelled honest, once on each; these calls are counted apart from the 109. All 41 are accepted. By the record of the runs that made them, the `cp_prove` that made the timed runs' proofs (from which sources it was built: [docs/limits.md, "What was run on these programs, and what was not"](../docs/limits.md#what-was-run-on-these-programs)), and not the prover of those 42, made them, in 3 runs, each under a commitment of its own. They are taken from 363 of the 723 proofs made in these runs, as reported: those of each run's first service, and each run's one proof that covers 1,001 positions. The rule is their own, fixed beforehand, and uses no verdict of either verifier: each run's one proof that covers 1,001 positions and, of that run's first service's proofs by number, every ninth from the first on, the first 13, 13 and 12 of them: 41 in all. All are at exact match and at full size, on synthetic weights as reported. They prove 14 requests, 7 of which are also among those of the 47, at 2 pairs of prompt and output length. The three configuration files given at these calls are, by checksum, those of this repository's stored full-size set. `cp_verify` had accepted each of the 723 when its run checked it, as reported, and the command had accepted each of these 41 before, over Lean files that differ from this repository's. What these calls are, and what the run does not show: [GAPS.md](GAPS.md), "Runs and counts" and entries 14 and 76.
