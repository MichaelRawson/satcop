#!/bin/sh

rm -rf satcop.zip bin/
mkdir bin/
docker build . -t satcop
container=`docker create satcop`
docker cp $container:/target/release/satcop bin/satcop
docker rm $container
strip bin/satcop
cp etc/starexec_run_default bin/
zip satcop.zip -r bin/
rm -rf bin/