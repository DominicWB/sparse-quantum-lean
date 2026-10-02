# Release checklist

1. Confirm the software authors in `CITATION.cff` (currently Dominic W. Berry
   only), and set the release version consistently in `lakefile.toml`,
   `README.md`, `CITATION.cff` and `scripts/release_manifest.json`. If source
   or configuration files change, review those changes and update their
   hashes in the release manifest.
2. Publish the clean source tree and require green CI on the exact commit.
   CI runs the packaging check, `lake build`, all 588 axiom audits and a
   check that the build preserves the dependency pins.
3. Add the real repository URL to the citation metadata and enable a README
   CI badge. Require CI on the final commit, then tag it `v1-arxiv` (or the
   tag matching the paper version).
4. Archive the tagged release with Zenodo or another suitable archive.
   Cite the actual repository URL, tag/commit and archival identifier in
   the paper. Include the toolchain versions and the formalisation scope.

An ancillary source archive can be made from the checked tag:

```sh
git archive --format=tar.gz --prefix=sparse-quantum-lean/ v1-arxiv > sparse-quantum-lean.tar.gz
```

Include the complete source tree, toolchain, Lake manifest and licence.
Exclude `.lake`, compiled objects and local working logs. For an initial
upload, extract the source ZIP into an empty folder and initialise Git there.
A public CI run supplies build evidence; historical development logs are not
part of the release package.
