#!/bin/bash

# トークン更新
response=$(curl https://api.dropbox.com/oauth2/token \
    -d grant_type=refresh_token \
    -d refresh_token=P2mONEKzZAYAAAAAAAAAATHry5byz8ieD9eKh_0QN41CppKWLvrpmEEoDB4VjchK \
    -u 1gasnizrljzobqv:akg6iqajij5rpqn)
DROPBOX_TOKEN=$(echo $response | jq -r '.access_token')
export DROPBOX_TOKEN

# verify
cd ~/ac2/lib/library
oj-verify run
#cp ./.verify-helper/timestamps.local.json ./.verify-helper/timestamps.remote.json