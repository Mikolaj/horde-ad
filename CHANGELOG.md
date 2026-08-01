# Revision history for horde-ad

## [v0.4.0.0](https://github.com/Mikolaj/horde-ad/compare/v0.3.0.0...v0.4.0.0)

- Sort a gather's slice dimensions in the contraction pass, cutting time and
  allocation on gather-heavy programs (issue #123)
- Add convVjpBench, a criterion suite for convolution gradients, with
  deterministic correctness tests and poor man's benchmarks beside it
- Export more of Core.AstSimplify and Core.AstTraverse
- Split CI in two, so that formatting and the optimized suites are checked
  as well, and make the test_seq flag actually sequence the suite
- Add document-verification tooling under tools/ and the CLAUDE.md guidance
  files it checks

## [v0.3.0.0](https://github.com/Mikolaj/horde-ad/compare/v0.2.0.0...v0.3.0.0)

- Extensive performance rework
- Update to new versions of ox-arrays, orthotope and dependent-enummap
- Minor polish of the API

## [v0.2.0.0](https://github.com/Mikolaj/horde-ad/compare/v0.1.0.0...v0.2.0.0)

- Modernize the dep (ilist) that provides imap to make Stackage happy
- Make the cabal sublibraries public, as intended
- Tweak benchmarks

## [v0.1.0.0](https://github.com/Mikolaj/horde-ad/compare/v0.0.0.0...v0.1.0.0)

- First version. Released on an unsuspecting world.
