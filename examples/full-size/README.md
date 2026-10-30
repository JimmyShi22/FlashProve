# A full-size proof that the verifier accepts

One proof at the size of Llama 4 Maverick, on synthetic weights, with the public files that the verifier needs to check it. The programs make these weights up themselves; no weight file of Meta's was used. A few constants in `config/` go back to work on real models: see [How the files were made](#how-the-files-were-made). It shows what a client of the full-size model downloads and runs. No GPU is needed. Read [../accepted-proof/](../accepted-proof/README.md) first: the files are named as there.

## Try it

From the repository's top directory, after `verifier/build.sh`. As in the small example, the commitment ID after `-id` comes with the example; in a real check it must not. The call below runs without `-j`, that is, with one thread for its longest stage. Have at least 4 GiB of memory free. It takes longer than the small example's call, and how long varies with the machine and its load: two sets of 8 calls (not on the released programs; each set with a `cp_verify` built from [other sources](../../docs/glossary.md#other-sources)) on a shared machine with 24 virtual CPUs took 36.2 to 44.0 seconds and 43.5 to 66.2 seconds, and in the first set the call's processes held about 3,400 MiB at the largest sample (row `verify-time-example` of [docs/figures.tsv](../../docs/figures.tsv)).

```sh
bin/cp_verify examples/full-size/config examples/full-size/ivk \
  examples/full-size/example.req examples/full-size/example.y \
  examples/full-size/example.proof \
  -id 7a285919b43961861d9839530c26725accf26aa6d74e3c2afa31b9dc6bcd18fe -q
```

The call ends with exit code 0. Its last four lines:

```
commitment: 86 closeness rounds of the one-time files rest on another source than the bound within a third of the distance; the table has a record: the binding of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given
proof of work: up to 32 bits counted in 71 rounds; with it the least round has 128.00 bits, without it 96.23 bits
result-v1 status=0 claim=exact-match id=7a285919b43961861d9839530c26725accf26aa6d74e3c2afa31b9dc6bcd18fe bits=128 work=32 work-rounds=71 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=86 record=1 r=23 e=1024 T=1024 tokens=24..1023 y=yes policy=exact-match C=256 theta=256 cap=0 s=15 sh=8 sT=4 F=24 above-clip=0 leaf=0 stages=key,leaf,request dw=8 build=<64 hex digits>
YES
```

The last line is the answer. This configuration counts proof of work toward the target, and the word `YES` does not tell that it was counted. The three lines above it say more:

- `proof of work:` says how many bits were counted, and then gives two figures: how many bits the weakest round has with them, and how many the weakest has without them. Each is a single round's figure, by the verifier's own count, which covers a cheating prover's single try, not repeated tries. Neither is a security level.
- `result-v1` is for programs ([verifier/docs/output.md](../../verifier/docs/output.md)). Its fields `least-round=` and `least-round-without-work=` are those two figures. Its field `bits=128` is a requirement, the bits that the call asks for (128, unless `-bits` asks for another number); the weakest round meets it only with up to 32 bits of proof of work counted by assumption, and with no margin. These printed bits are the C++ programs' own accounting, not a theorem. The proved figure is the Lean theorem's, about 124 bits per hash query, with a floor of about 2^-101, and it is of the verifier written in Lean, not of `cp_verify` ([guide/what-is-proved.md](../../guide/what-is-proved.md)).
- `commitment:` says on what the binding of the weights rests. Its number counts the closeness rounds of the key file and the leaf file (`ivk/key.bin`, `ivk/leaf/0.bin`) that do not rest on [the bound within a third of the distance](../../docs/glossary.md#proved-lemma); "the table has a record" says that the committed tables have published [out-of-domain (OOD) answers](../../docs/glossary.md#record) (masked sums of the weights), by the parameter file's line `record 1`. The fields `commitment-assumed-rounds=` and `record=1` of the line `result-v1` say the same for programs.

The bounds that the programs print for the truth of an accepted request and for the binding of the weights rest on the theorem on codes named in the line `commitment:`, taken as given. At the default setting they do so with no bits to spare, and lean on counted proof of work in the rounds that draw positions. They also rest on BLAKE2b, taken as a random oracle, and on an argument on paper, in a technical report that is not public and not refereed, whose conditions no complete set of parameters of any size is known to meet. Neither bound is proved of the programs. [docs/limits.md](../../docs/limits.md#what-the-theorem-assumes) gives all that these bounds rest on, and what has been checked of it and what has not.

## What the YES says

The request holds 1,024 tokens, then r = 23 and e = 1024. Tokens 0 to 23 are the prompt. The proof states that tokens 24 to 1023 and the token after the request, 52599 (in `example.y`), are each the token that the committed model ranks first after the tokens before it: 1,001 tokens in one proof.

The model has Maverick's shape (48 layers, 128 routed experts) and none of its weights: they come from a generator. So this `YES` shows how large the files of a full-size proof are and what checking one costs on your machine. Like the small example's, it says nothing about any model that anyone serves. Your part in a real check is described in [../accepted-proof/](../accepted-proof/README.md#what-the-yes-says).

## How the files were made

At the configuration [prover/examples/target_full_f2](../../prover/examples/target_full_f2), on one H100, with calls like the two in [../accepted-proof/README.md](../accepted-proof/README.md#how-the-files-were-made): `cp_commit` also got `-keep-for-the-audit`, and `cp_prove` also got `-in-step 1 -memory lean`. `-memory lean` lays out the GPU's memory in another way; by the program's own help the proofs stay the same. These files were not made by the released programs, so they show nothing of the released prover. `cp_commit` drew the seed. The secret directory of this example is not part of the repository. We cannot show that no copy of it exists; the weights are synthetic, so nothing depends on it. `ivk/` holds `key.bin` and the one stored copy's file that this proof names, `leaf/0.bin`.

Before any call of `cp_prove`, the audit script that came with the programs that made the files, `tools/audit/audit_commitment.sh`, audited the commitment, and it passed; a pass covers little. It compared 10.22 % of the bytes of `ivk/key.bin` and `ivk/leaf/0.bin` by value; no false kept bytes were tried ([what a YES does not cover](../../tools/audit/README.md#what-a-yes-does-not-cover); row LIM-63 of [the table of all rows](../../docs/limits-all-rows.tsv)).

A few lines of `config/policy.txt` (`s`, `eps1_lo`, `eps2_lo`, `epsF_lo`) hold values that come from work on fits to Llama 4 Maverick's weights in a third party's public 4-bit GGUF conversion (the five files of examples/maverick/weights.sha256, by the checksums on record, not compared with the public page; of the three passes over these weights behind the line `s`, that the third read these files is likely, not shown). `config/KL.bin` holds constants: each of its fields of scales has one value in every layer, as anyone can see who decodes the file. By the authors' own records, which are not in this repository, so that a reader cannot check them, the constants were typed by hand, to suit the ranges of the values that the programs' generator of synthetic weights gives. That none of them was picked with a fit to Llama 4 Maverick in view is not shown: when they were typed, ranges of scales were known that came from fits to a different model, Meta's Llama 2 7B, and so was a second set of ranges, for the norms' constants and for the attention shift, whose origin is not established (it is not known whether Llama 4 Maverick's weights had a part in it). The attention shift in `config/KL.bin` (its field `sh`, 8 in every layer; not the line `sh 8` of `config/policy.txt`) very likely stems from Llama 2 7B (that is inferred). It is not known whether the second set had a part in that field, whether the known ranges shaped any other field of `config/KL.bin`, why the norms' constants in it (`M1` = `M2` = 44) have their value, or whether any model's weights had a part in choosing the lines `MF` and `KF` of `config/policy.txt`. [THIRD_PARTY.md](../../THIRD_PARTY.md) lists further lines and entries (among them the `rp` flags, and the line `sh 8` with the lines that follow from it); where the lines and entries come from that it does not name is, line by line, not known either.

`example.req`, a copy of [own_choices.req](../../prover/examples/target_full_f2/own_choices.req), holds a prompt of 24 tokens and then 1,000 tokens that the integer model chose itself, one after another: each is its greedy choice after the tokens before it, and `example.y` is its choice after the last. The tokens were chosen with the integer-model package's `IntegerModel.extend`. [Its README, "A request from the model's own reply"](../../integrations/vllm/integer_model/README.md#a-request-from-the-models-own-reply), prints the same loop for the small example; the script that drove it at full size is not in this repository.

The route on Llama 4 Maverick's own weights is in [../maverick/](../maverick/README.md).
