# Security Policy

## Supported Versions

The project is pre-1.0. Security fixes are applied to the `develop` branch and carried into the next release tag.

## Reporting a Vulnerability

Please do **not** open a public GitHub issue for security vulnerabilities.

Report vulnerabilities privately via [GitHub Security Advisories](https://github.com/mumei-lang/mumei-lean/security/advisories/new) ("Report a vulnerability"). If private vulnerability reporting is not yet enabled on this repository, contact the maintainer via their GitHub profile (https://github.com/AkiraTamai) instead of opening a public issue.

Please include:

- A description of the issue and its potential impact
- Steps to reproduce or a proof of concept
- Affected versions/commits, if known

We aim to acknowledge reports within 7 days and will coordinate disclosure timing with the reporter.

## Scope Notes

- The bridge scripts parse `.proof-cert.json` files and generate Lean sources; crafted certificates or `.mm` content that escapes `generated/` (path traversal, tactic injection into generated modules) are in scope.
- `.lean-cert.json` certificates are a trust boundary: a path that marks an unproven atom `lean_verified`, or defeats the stale-translator/version gates, is a security issue.
