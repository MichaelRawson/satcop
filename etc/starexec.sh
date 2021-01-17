#!/bin/sh

CARGO_PROFILE_RELEASE_LTO=fat
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
CARGO_PROFILE_RELEASE_DEBUG=0
CARGO_PROFILE_RELEASE_PANIC="abort"
TARGET=x86_64-unknown-linux-musl
cargo build --release --target $TARGET
LAZYCOP=target/$TARGET/release/lazycop2

rm -rf lazycop.zip bin/
mkdir bin/
strip $LAZYCOP
cp $LAZYCOP bin/
cp etc/starexec_run_default bin/
zip lazycop.zip -r bin/
rm -rf bin/
