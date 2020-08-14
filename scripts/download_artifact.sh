#!/bin/sh

mkdir -p docs/html/docs
cd docs/html/docs
curl -v -L -H "Accept: application/vnd.github.v3+json" -H "Authorization: token $GITHUB_TOKEN" https://api.github.com/repos/ymherklotz/vericert/actions/artifacts/14069960/zip -o html-documentation.zip
unzip html-documentation.zip
rm html-documentation.zip
cp ../../css/coqdoc.css .
