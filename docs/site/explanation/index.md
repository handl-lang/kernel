# Explanation

## Why this crate exists

Everything above the kernel has to agree on what a language *is* and what a
value *is*; the kernel is that agreement and nothing else. It was extracted from
the `host` workspace (ADR-0128) so a consumer can pin the substrate without
pulling the whole host, and it depends only on `hnl-engine` — which is why the
dependency arrows all point downwards.

## Where it sits

This crate belongs to the `engine-*` family. Plugins, kits and hosts reach it
through the kit's operation slot, so the engine can be swapped without touching a
language definition.

See the [reference](/kernel/reference/) for the API and the
[how-to guides](/kernel/how-to/) for tasks.
