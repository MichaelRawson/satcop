#!/bin/sh

CARGO_PROFILE_RELEASE_LTO=fat
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
CARGO_PROFILE_RELEASE_DEBUG=0
CARGO_PROFILE_RELEASE_PANIC="abort"
TARGET=x86_64-unknown-linux-musl
cargo build --release --target $TARGET
SATCOP=target/$TARGET/release/satcop
strip $SATCOP
exit 0

rm -rf lazycop.zip bin/
mkdir bin/
cp $SATCOP bin/
cp etc/starexec_run_default bin/
zip lazycop.zip -r bin/
rm -rf bin/
