#!/bin/sh

mkdir -p docs/html/proof
cd docs/html/proof
curl -v -L -H "Accept: application/vnd.github.v3+json" -H "Authorization: token $GITHUB_TOKEN" https://api.github.com/repos/ymherklotz/vericert/actions/artifacts/26286264/zip -o html-documentation.zip
unzip html-documentation.zip
rm html-documentation.zip
cp ../../css/coqdoc.css .
