+++
id = "I-001"
title = "dep drift — handl-pkg-vendor git-dep source missing, uncommitted Cargo.lock"
status = "in-progress"
created = "2026-10-31"
owner = "devin"
priority = "high"
+++

From bupha T-029 CI audit (2026-10-31): kernel has uncommitted Cargo.lock changes and a git-dep on handl-pkg-vendor whose source is missing. Fix the dependency and commit the lockfile.
