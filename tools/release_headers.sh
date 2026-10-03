#!/bin/sh
# Called only by the release job after verification and archive checks succeed.
set -eu
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_SHA:?}"
: "${RUNNER_TEMP:?}"
archive=${1:?archive path required}
current_sha=$(gh api "repos/$GITHUB_REPOSITORY/git/ref/heads/main" --jq '.object.sha')
if [ "$current_sha" != "$GITHUB_SHA" ]; then
    echo "Skipping superseded commit $GITHUB_SHA; main is now $current_sha"
    exit 0
fi
notes_file="$RUNNER_TEMP/header-release-notes.md"
printf 'Public headers only; verified commit: `%s`.\n\nDownload `library-hpp.zip` and extract it. The archive contains only `library/**/*.hpp`.\n' "$GITHUB_SHA" > "$notes_file"
if gh release view headers --repo "$GITHUB_REPOSITORY" > /dev/null 2>&1; then
    gh api --method PATCH "repos/$GITHUB_REPOSITORY/git/refs/tags/headers" \
        -f sha="$GITHUB_SHA" -F force=true > /dev/null
    gh release upload headers "$archive" --clobber --repo "$GITHUB_REPOSITORY"
    gh release edit headers --title "Verified library headers" --notes-file "$notes_file" \
        --latest --repo "$GITHUB_REPOSITORY"
else
    # A previous interrupted creation may have left the tag without a release.
    if gh api "repos/$GITHUB_REPOSITORY/git/ref/tags/headers" > /dev/null 2>&1; then
        gh api --method PATCH "repos/$GITHUB_REPOSITORY/git/refs/tags/headers" \
            -f sha="$GITHUB_SHA" -F force=true > /dev/null
    fi
    gh release create headers "$archive" --target "$GITHUB_SHA" \
        --title "Verified library headers" --notes-file "$notes_file" \
        --latest --repo "$GITHUB_REPOSITORY"
fi
