#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""check.py checks the Lean library in the parent directory.
scripts/README.md explains what each step shows and what it does not show. Read it before you quote
a result.

USAGE
  python3 -B scripts/check.py [--jobs N] [--wide-jobs N]   with elan and Lake; tested only on Linux
OPTIONS
  --only tree,words,imports   run only the listed steps. The steps: tree, words, imports, build
  --root DIR                  check another copy of the library
  --digest                    only print the sha256 of the library as it is now, to compare with the
                              one at the end of an earlier run. It does not cover the Lake files
  --jobs N                    number of parallel replay jobs. Default: one, and one more for each
                              2 GiB of available memory beyond 21, at most one per core and at
                              most 48. That count is a rule of thumb, not what the jobs need: on
                              a machine with less memory give a small number (CHECKING.md)
  --wide-jobs N               how many modules of AtFullSide/ and ShapeLines/ are replayed at a
                              time. Default: see LEAN_NUM_THREADS below. These processes are heavy:
                              one was seen to hold 39.4 GiB of its own (CHECKING.md)
  --other-lake                continue, knowingly, with Lake files other than the delivered ones:
                              see scripts/RULES.txt, "Lake files"
  --i-trust-every-account-on-this-machine
                              build also in a scratch directory that another account could change:
                              see below, and scripts/RULES.txt, "One copy"

ENVIRONMENT
  CHECK_SCRATCH_DIR           where the scratch directory is created (default: the system's
                              temporary directory): scripts/RULES.txt, "One copy"
  LEAN_NUM_THREADS            how many Lean processes "lake build" runs at a time, and how many
                              modules of AtFullSide/ and ShapeLines/ are replayed at a time, unless
                              --wide-jobs says that: --jobs, if lower, holds for these too, and
                              so does one, and one more for each 40 GiB of available memory beyond
                              50. Without it, or with anything but a whole number above 0: one, and
                              one more for each 12 GiB of available memory beyond 50, at most one
                              per core. The run prints the numbers
NEEDS
  at least 21 GiB of free memory, whatever --jobs: with less, the build is not started. The build
  takes far more: scripts/RULES.txt, "The build"; CHECKING.md, "What you can do, and on what
  machine"

RESULT. The last line starts with one of
  All steps passed: tree, words, imports, build (kernel replay, audit).
      exit status 0. It goes on to say what this script does not run
  Partial run passed (tree, words): only these steps were run
      exit status 0, with --only
  Check failed: words
      exit status 1, with the steps that failed
  Passed so far, and not the full check
      exit status 3: no step failed, but part of a step was not run or had nothing to check; the
      line "NOT RUN" above it says which
      (A run can end with status 0 although no theorem got a verdict on binders or on
      Classical.choice: that is so when every line of top-theorems.txt says general; the last line
      then says so.)
  The Lake files are not the ones that this check.py expects
      exit status 3 at best: see scripts/RULES.txt, "Lake files"
The lines above it, under "Particulars of this run:", identify the library and the checking tools by
sha256 and give the counts, what was not run and where the logs are. A wrong argument, a scratch
directory that cannot be used, or a lakefile.toml from which this script cannot read the thread
stacks gives a short message and exit status 2.
If another account could change the scratch directory's parent or a folder above it (a folder that
its group or others can write in without the sticky bit, or one that belongs to an account other
than yours or root; as root with SUDO_UID set, as sudo sets it, the account that ran sudo counts as
yours), a run with the step "build" refuses at its start: no step is run, nothing is built, and
the exit status is 1. This script reaches its scratch directory through a descriptor that it holds,
but Lake and Lean find it by paths of their own making, so that account could put another folder in
its place while the build runs. A folder that only you or root can change, such as one in your home
folder, or /tmp, with its sticky bit, will do. On a machine where you trust every account (a
container of your own, for example), --i-trust-every-account-on-this-machine takes such a folder all
the same, and the first and last lines say so. The text steps and --digest start no program, and
once the place is opened they do not go by the path: in such a place they print a note and go on, if
the named directory is there; a missing one is not made there (exit status 2).
A run with the step "build" also produces the listing: for each top theorem, the names that its
statement depends on, with the type and value of each, taken from the compiled files. That, not the
source, is what a reader should read.

MORE. scripts/README.md: what each step shows and what it does not show. scripts/RULES.txt: the
build, the Lake files and what their pins do not give you, the scratch directory, how the script
was tested, and how the text rules work."""

import os, sys

HERE0 = os.path.dirname(os.path.realpath(__file__))
# The run's last lines identify the checking tools by sha256, so the code that is hashed must be the
# code that runs. This file's directory is removed from the module search path (a file there named
# like a standard module would run in its place), and lclib.py is read once: the same text is hashed
# and executed ("import" could run a stale compiled copy, and would write one).
sys.path[:] = [p for p in sys.path if os.path.realpath(p) != HERE0]
import argparse, atexit, builtins, concurrent.futures, hashlib, json, re, resource, secrets
import shutil, stat, subprocess, time, types


def plain(s):
    """Returns s with every character for which str.isprintable() is false, except the tab, written
    as an escape such as \\x1b: control characters (line breaks too), direction marks and other
    invisible format characters, separators other than the space, surrogates, unassigned code
    points. Not escaped: right-to-left letters, blank letters such as U+3164, combining marks."""
    if s.isprintable():
        return s
    return ''.join(
        c if c.isprintable() or c == '\t' else c.encode('unicode_escape').decode('ascii') for c in s
    )


def print(*parts, **how):
    """Everything that check.py prints, except argparse's messages and a traceback, goes through
    here and through plain(), so one call prints one line. Much of the text comes from the library
    (file names, lines of text) or from Lake and Lean, and none of it may start a line of its own,
    move the cursor or change colours."""
    builtins.print(*(plain(str(x)) for x in parts), **how)


LCLIB = open(HERE0 + '/lclib.py', 'rb').read()
lclib = types.ModuleType('lclib')
exec(compile(LCLIB, HERE0 + '/lclib.py', 'exec'), lclib.__dict__)
ap = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
ap.add_argument('--root')
ap.add_argument('--only')
ap.add_argument('--digest', action='store_true')
ap.add_argument('--other-lake', action='store_true')
ap.add_argument('--i-trust-every-account-on-this-machine', action='store_true')
ap.add_argument('--jobs', type=int, default=0)
ap.add_argument('--wide-jobs', type=int, default=0)
ap.add_argument('--help', '-h', action='store_true')
a = ap.parse_args()
if a.help:
    for l in __doc__.split('\n'):
        print(l)
    sys.exit(0)
ME = os.path.realpath(__file__)  # taken here, while the working directory is still the caller's
HERE = os.path.dirname(ME)
SRC = os.path.realpath(a.root) if a.root else os.path.dirname(HERE)
STEPS = ['tree', 'words', 'imports', 'build']
only = a.only.split(',') if a.only else STEPS
if set(only) - set(STEPS):
    print(
        (
            'check.py: --only names %s, which is not a step. The steps are: '
            '%s. Nothing was created or checked.'
        )
        % (', '.join(repr(x) for x in sorted(set(only) - set(STEPS))), ', '.join(STEPS)),
        file=sys.stderr,
    )
    sys.exit(2)


def temporary():
    """The first of TMPDIR, TEMP, TMP, /tmp, /var/tmp and /usr/tmp that is a directory in which this
    account may make an entry. Nothing is written to find that out. Raises FileNotFoundError if none
    of them is."""
    named = [os.environ.get(k) for k in ('TMPDIR', 'TEMP', 'TMP')]
    for d in named + ['/tmp', '/var/tmp', '/usr/tmp']:
        if d and os.path.isdir(d) and os.access(d, os.W_OK | os.X_OK):
            return d
    raise FileNotFoundError


# The scratch directory is created (random name, mode 700) in CHECK_SCRATCH_DIR or in the system's
# temporary directory. Symbolic links in that path are resolved once, here. It must not lie inside
# the library: the copy would include itself.
try:
    NAMED = os.path.abspath(os.environ.get('CHECK_SCRATCH_DIR') or temporary())
    BASE = os.path.realpath(NAMED)
except OSError:
    print(
        (
            'check.py: this system has no usable temporary directory. Set '
            'CHECK_SCRATCH_DIR to a directory. Nothing was created.'
        ),
        file=sys.stderr,
    )
    sys.exit(2)
if (BASE + '/').startswith(SRC + '/'):
    print(
        (
            'check.py: the scratch directory would be created in %s, which '
            'is inside the library to be checked, %s, so the copy would '
            'contain itself. Nothing was created. Set CHECK_SCRATCH_DIR '
            '(or TMPDIR) to a directory outside the library.'
        )
        % (BASE, SRC),
        file=sys.stderr,
    )
    sys.exit(2)


# The accounts whose directories this run may work in: this one, root, and under sudo (as root, with
# SUDO_UID set) the account that ran sudo, so that its own directories, such as its home, do not
# count as another account's.
OWNERS = {0, os.geteuid()}
if os.geteuid() == 0 and re.fullmatch('[0-9]+', os.environ.get('SUDO_UID', '')):
    OWNERS.add(int(os.environ['SUDO_UID']))


def others_in_group(gid):
    """False if the system's lists of accounts and groups show only accounts of OWNERS in the
    group; True otherwise, also if they do not know the group or this account. Many systems give
    each user a group of their own, so directories that such a group may write are common and
    harmless."""
    import grp, pwd

    try:
        names = set(grp.getgrgid(gid).gr_mem) | {
            u.pw_name for u in pwd.getpwall() if u.pw_gid == gid
        }
        return not names <= {pwd.getpwuid(u).pw_name for u in OWNERS}
    except KeyError:
        return True


def open_to_others(d, made=True):
    """Returns the lowest directory, from d up to the root, in which another account could rename or
    remove an entry, and the reason, or None: one whose owner is not among OWNERS,
    or one without the sticky bit that everybody, or a group with other accounts, may
    write. A symbolic link is judged by its owner alone (its mode says nothing), and by the
    directories above it. With made=False the end of d need not exist yet: the look begins at the
    lowest part that does. Access control lists are not looked at."""
    while not made and not os.path.lexists(d):
        d = os.path.dirname(d)
    while True:
        try:
            s = os.lstat(d)
            if s.st_uid not in OWNERS:
                return d, (
                    'a symbolic link that belongs to another account'
                    if stat.S_ISLNK(s.st_mode)
                    else 'owned by another account'
                )
            if (
                not stat.S_ISLNK(s.st_mode)
                and not s.st_mode & stat.S_ISVTX
                and (s.st_mode & 0o002 or (s.st_mode & 0o020 and others_in_group(s.st_gid)))
            ):
                return d, 'its group or others can write in it, and it has no sticky bit'
        except OSError:  # it was there a moment ago: another account has moved it
            return d, 'it was moved or removed while this run looked at it'
        if d == os.path.dirname(d):
            return None
        d = os.path.dirname(d)


# This script reaches its scratch directory through a descriptor that it holds, and as its working
# directory, never by the path: whoever can rename a directory above it changes nothing for the text
# steps, so for them such a place is a note (a named directory that is missing is not made there:
# status 2). Lake and Lean start in that working directory, but what
# paths they build from it no script can bound, and they compile and run what they find: in such a
# place a run with the step "build" refuses: at the first look before anything is made, at the
# second before the scratch directory is made (refuse; step_build has the same test once more).
# The library's own directory no script can guard.
INSTRUCTION = 'scripts/RULES.txt, "One copy"'
SAID = ''  # what the first and the last line of a run gain if the option was needed


def look(made):
    """open_to_others, of the place as it was named, of what each symbolic link on the way names
    (and each link on the way to that), and of the place as it is with its links resolved."""
    ways, i = [NAMED], 0
    while i < len(ways) and i < 40:
        found = open_to_others(ways[i], made and i == 0)
        if found:
            return found
        q = ''
        for part in ways[i].split('/')[1:]:
            q += '/' + part
            if os.path.islink(q):
                # The link's text is kept as it is: ".." behind a further link means that link's
                # target, so it must not be cut out of the text.
                to = os.path.join(os.path.realpath(os.path.dirname(q)), os.readlink(q))
                if to not in ways:
                    ways.append(to)
        i += 1
    if i < len(ways):
        return ways[i], 'this script does not follow so many symbolic links, so it cannot tell'
    return open_to_others(BASE, made)


def refuse(shared):
    """Ends a run that has the step "build", with status 1, if another account could change the
    place of the scratch directory and the caller has not said that every account is trusted."""
    if not shared or a.digest or 'build' not in only or a.i_trust_every_account_on_this_machine:
        return
    print(
        'check.py: the scratch directory would lie below %s, which another account may be able to '
        'change (%s): it could put another folder in the scratch directory\'s place while the '
        'build runs and choose what Lean compiles and runs as you. Name a new scratch directory '
        '(CHECK_SCRATCH_DIR) below folders that only you or root can change (such as one in your '
        'home folder, or in /tmp, whose sticky bit keeps others from replacing it), %sor, if you '
        'trust every account on this machine, say so with '
        '--i-trust-every-account-on-this-machine; no step was run, and nothing was built'
        % (
            shared
            + (
                (
                    ''
                    if os.geteuid() == 0
                    else 'or, if %s is yours, close it ("chmod go-w" on it is enough), ' % shared[0]
                ),
            )
        ),
        file=sys.stderr,
    )
    sys.exit(1)


DIRECTORY = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
try:
    # For the whole run: whatever it creates is for this account alone, and usable by it, whatever
    # umask the caller has. check.py writes only into its scratch directory.
    os.umask(0o077)
    # The first look comes before anything is written, at the part of the path that exists.
    SHARED = look(False)
    refuse(SHARED)
    if SHARED and not a.i_trust_every_account_on_this_machine:
        # No directory is made where another account could lead the making astray.
        if not os.path.isdir(BASE):
            raise PermissionError(
                13,
                'this run finds no directory there, and it makes none where another account may be '
                'able to change %s (%s)' % SHARED,
            )
    else:
        os.makedirs(BASE, exist_ok=True)
    # The second look: where directories were made, every directory of the path exists now, and one
    # that another account made in the meantime is seen by its owner.
    SHARED = SHARED or look(True)
    refuse(SHARED)
    if SHARED and not a.i_trust_every_account_on_this_machine:
        print(
            'check.py: note: another account may be able to change %s (%s), under which this run '
            'works. Once it has opened that place, this run reads and writes through descriptors '
            'that it holds, not by the path; a run with the step "build" would refuse there: see '
            '%s.' % (SHARED + (INSTRUCTION,)),
            file=sys.stderr,
        )
    if SHARED and a.i_trust_every_account_on_this_machine:
        SAID = (
            '; the scratch directory lies below %s, which other accounts could change: the caller '
            'said that every account on this machine is trusted '
            '(--i-trust-every-account-on-this-machine)' % SHARED[0]
        )
    # The place is held from here on: the scratch directory is made, opened and at the end removed
    # as an entry of this descriptor, and the path to it is not walked again.
    BASE_FD = os.open(
        BASE, DIRECTORY | getattr(os, 'O_PATH', 0)
    )  # with O_PATH it need not be readable
    while True:
        NAME = 'lean-check-' + secrets.token_hex(4)
        try:
            os.mkdir(NAME, 0o700, dir_fd=BASE_FD)
            break
        except FileExistsError:
            pass
    OUT = BASE + '/' + NAME  # for the messages, and for nothing else
except OSError as e:
    print(
        ('check.py: cannot create a scratch directory in %s (%s). Nothing ' 'was checked.')
        % (BASE, e.strerror),
        file=sys.stderr,
    )
    sys.exit(2)
# Whatever this run reads, writes, removes or makes writable in its scratch directory it reaches
# through this descriptor, or relative to the working directory, which is the same directory: if
# another account put something else at the path, that would be neither read nor touched.
# What is opened must be what was just made: this account's, closed to group and others, empty. No
# other account can make such a directory. (Where another account can rename the entries of the
# place, it could put another empty, closed directory of this account's own at the name between the
# two calls; the test does not tell the two apart.)
try:
    OUT_FD = os.open(NAME, DIRECTORY, dir_fd=BASE_FD)
    _s = os.fstat(OUT_FD)
    made = _s.st_uid == os.geteuid() and not _s.st_mode & 0o077 and not os.listdir(OUT_FD)
except OSError:
    made = False
if not made:
    print(
        'check.py: the scratch directory %s is not as this run made it (yours, closed to group and '
        'others, empty): another account may have replaced it, or this file system does not keep '
        'modes. Nothing was checked. Name another place with CHECK_SCRATCH_DIR.' % OUT,
        file=sys.stderr,
    )
    sys.exit(2)
os.fchdir(OUT_FD)
ROOT = 'tree'  # relative to the working directory, which is the held scratch directory
os.mkdir('tree', dir_fd=OUT_FD)


def fresh(rel, anew=False):
    """Opens the file rel (relative to the scratch directory, "/" between its parts) for writing and
    returns the descriptor. Each directory on the way is made if it is missing, and opened without
    following a link; no link at the file's own name is followed. With anew=True the call fails if
    anything lies at that name; otherwise a file that is there is emptied."""
    fd = os.dup(OUT_FD)
    try:
        *dirs, name = [p for p in rel.split('/') if p not in ('', '.')]
        for d in dirs:
            try:
                os.mkdir(d, dir_fd=fd)
            except FileExistsError:
                pass
            fd, above = os.open(d, DIRECTORY, dir_fd=fd), fd
            os.close(above)
        how = os.O_EXCL if anew else os.O_TRUNC
        return os.open(name, os.O_WRONLY | os.O_CREAT | os.O_NOFOLLOW | how, 0o600, dir_fd=fd)
    finally:
        os.close(fd)


def put(src, rel):
    """Copies the file src to rel in the scratch directory (fresh, anew): the copy lands in the
    directory that this run holds, and overwrites nothing, whatever lies at its path by now. If
    something lies at rel already, it prints a message and ends the run with exit status 2."""
    try:
        new = fresh(rel, anew=True)
    except FileExistsError:
        print(
            'check.py: in the scratch directory %s something already lies at %s: another process '
            'put it there, or this file system takes two names of the library for one. Nothing '
            'was checked.' % (OUT, rel),
            file=sys.stderr,
        )
        sys.exit(2)
    with open(new, 'wb') as o, open(src, 'rb') as i:
        shutil.copyfileobj(i, o)


def remove(name, fd):
    """Removes the entry name, with all that is below it, from the directory that is open at fd.
    What cannot be removed stays, for example a directory that its owner may not read."""
    try:
        try:
            sub = os.open(name, DIRECTORY, dir_fd=fd)
        except OSError:  # not a directory
            os.unlink(name, dir_fd=fd)
            return
        try:
            if os.fstat(sub).st_dev != os.fstat(fd).st_dev:
                return  # another file system is mounted here: it is not entered, and it stays
            try:
                os.fchmod(sub, 0o700)  # the copy keeps the packages' modes, also read-only ones
            except OSError:
                pass  # a file system without modes
            for n in os.listdir(sub):
                remove(n, sub)
        finally:
            os.close(sub)
        os.rmdir(name, dir_fd=fd)
    except OSError:
        pass


def away(what):
    """Removes the scratch directory (what is OUT) or the copy in it (what is ROOT). The last step,
    the removal of the emptied OUT, takes its entry out of the held directory above it, and only if
    that entry is still the directory that this run holds. Returns a short phrase for the end of the
    output."""
    for n in ['tree'] if what == ROOT else os.listdir(OUT_FD):
        remove(n, OUT_FD)
    if what == OUT:
        try:
            if os.path.samestat(
                os.stat(NAME, dir_fd=BASE_FD, follow_symlinks=False), os.fstat(OUT_FD)
            ):
                os.rmdir(NAME, dir_fd=BASE_FD)
        except OSError:
            pass
    try:
        left = os.fstat(OUT_FD).st_nlink > 0 if what == OUT else os.path.lexists(ROOT)
    except OSError:
        left = False  # a file system that no longer knows a directory once it is removed
    return (
        'could not be removed and is still there: ' + (OUT if what == OUT else OUT + '/tree')
        if left
        else 'has been removed'
    )


# A run that starts no program also removes its scratch directory after Ctrl-C or an error in this
# script.
# A run with the build does not: processes of Lake and Lean may still be writing there.
if a.digest or 'build' not in only:
    atexit.register(away, OUT)
failed, notrun, counts, tools, odd_things = [], [], {}, {}, []
DATAFILES = [
    'IMPORTS.txt',
    'top-theorems.txt',
    'choice-allow.txt',
    'scan-exceptions.txt',
    'claimed-theorems.tsv',
    'RULES.txt',
    'guards.txt',
    'front-statements.txt',
    'long-lines.txt',
    'listing-for.txt',
]  # listing-for.txt and choice-allow.txt may be absent; without one of the others the verdicts that
# need it fail. An absent file does not enter the library's sha256


def there(rel):
    """True if rel, a Lake file or a data file of the library, is a regular file. A symbolic link is
    not followed: it is recorded in odd_things, which makes the step "tree" fail, and counts as
    absent."""
    if os.path.islink(SRC + '/' + rel):
        odd_things.append(
            ('a file that is a symbolic link (not followed; it counts as ' 'absent): ') + rel
        )
        return False
    return os.path.isfile(SRC + '/' + rel)


# The checking tools, each identified by its sha256 at the start of the run: a tool that is changed
# during the run must not be reported under the sha256 of its later text.
tools['check.py'] = lclib.sha(open(ME, 'rb').read())[:12]
tools['lclib.py'] = lclib.sha(LCLIB)[:12]

AUDIT_TEXT = open(HERE + '/Audit.lean.in', encoding='utf-8').read()
# read once: the text that is hashed is the text that is used
tools['Audit.lean.in'] = lclib.sha(AUDIT_TEXT.encode('utf-8'))[:12]


def pin_shape(name, v):
    """Stops the run unless a pinned value has the shape that the script relies on. The pinned
    values stand between two marker lines each; a program lays them when a pinned file changes."""
    h = lambda x: isinstance(x, str) and re.fullmatch('[0-9a-f]{64}', x)
    word = lambda x: isinstance(x, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'!?]*", x)
    ok = {
        'LAKE_FILES': lambda: isinstance(v, dict)
        and sorted(v) == ['lake-manifest.json', 'lakefile.toml', 'lean-toolchain']
        and all(h(x) for x in v.values()),
        'KINDS': lambda: isinstance(v, dict)
        and sorted(v) == ['closed', 'general', 'headline']
        and all(type(x) is int and x >= 0 for x in v.values()),
        'NO_ROWS': lambda: isinstance(v, list) and all(word(x) for x in v),
        'WIDE_REPLAY': lambda: isinstance(v, list) and len(v) == 1 and all(word(x) for x in v),
        'WIDE_SUMS': lambda: isinstance(v, dict) and all(word(k) and h(x) for k, x in v.items()),
        'GOAL_SUMS_TEXT': lambda: isinstance(v, str)
        and all(
            re.fullmatch(r'[0-9a-f]{64} [A-Z][A-Za-z0-9_]*(?:/[A-Z][A-Za-z0-9_]*)*[.]lean', x)
            for x in v.split('\n')
            if x
        ),
        'GUARD_SUMS_TEXT': lambda: isinstance(v, str)
        and all(
            re.fullmatch(r'[0-9a-f]{64} [A-Z][A-Za-z0-9_]*(?:/[A-Z][A-Za-z0-9_]*)*[.]lean', x)
            for x in v.split('\n')
            if x
        ),
    }.get(name, lambda: h(v))()
    if not ok:
        print('check.py: the pinned value %s has not the shape that this script expects' % name)
        sys.exit(2)


# The sha256 of the three Lake files as delivered. They choose the Lean and the Mathlib that check
# the library, so they are compared, not only printed (limits: "What the pinned Lake files do not
# give you" in scripts/RULES.txt). After a change to one of them, put its new sha256 here.
# PINS: BEGIN
LAKE_FILES = {
    'lakefile.toml': 'dc70647e1279f5f82ae31066bc677f5d0082f6cd2d8d1164f84e0041eed572ed',
    'lake-manifest.json': '12a047fd42eb020bee9a938b42a9552f8334dcf702524774dc1b359d2c6c4e17',
    'lean-toolchain': '7dc000621e0046d1aada809e2b7177e64454645cf4c741e9daaf79c99ec2e7a2',
}
# PINS: END
pin_shape('LAKE_FILES', LAKE_FILES)
lake_other, lake_code = (
    {},
    {},
)  # file: what is wrong with it. lake_other: --other-lake lets it pass; lake_code: nothing does
# The library's Lake files choose the Lean, the Mathlib and the options, and they also decide what
# is built at all. They are copied here, at the same time as the library. The sha256 that is
# reported, and compared, is that of the copy.
for f, want in LAKE_FILES.items():
    if there(f):
        put(SRC + '/' + f, 'tree/' + f)
        raw = open(ROOT + '/' + f, 'rb').read()
        got = lclib.sha(raw)
        tools[f] = got[:12]
        try:
            name = raw.decode('utf-8').split('\n', 1)[0].strip()
        except UnicodeDecodeError:
            name = ''
        if f == 'lean-toolchain' and not (name and name.isprintable()):
            lake_code[f] = (
                'the Lake file lean-toolchain cannot be read as UTF-8 text, or its first line is '
                'blank or holds a character that cannot be printed (a tab inside the name, a byte '
                'order mark). Rejected even with --other-lake: elan, which starts Lake, may treat '
                'a file that names nothing as absent (not tried). Put the delivered file back, or '
                'write the name of a Lean, and nothing else, into its first line'
            )
        elif got != want:
            lake_other[f] = 'the Lake file %s has the sha256 %s; this check.py expects %s' % (
                f,
                got,
                want,
            )
    else:
        # Not even --other-lake lets this pass: the copy would lack the file. With no lean-toolchain
        # in the copy, elan, which starts Lake, takes a file of that name from a directory above it
        # (seen with elan 4.2.4), and in /tmp any account can put one there. What Lake does without
        # one of the other two was not tried.
        lake_code[f] = (
            'the Lake file %s is absent (or is a symbolic link, or not a '
            'regular file); this check.py expects it with the sha256 %s. '
            'Rejected even with --other-lake, which is for a file with other '
            'contents: Lake is not called on a copy that lacks the file. Put the '
            'delivered file back (a fresh copy of the library has it); if you did '
            'not remove it yourself, this is not the delivered library'
        ) % (f, want)
# Lake runs a lakefile.lean as a program when it loads the project (where a directory has both, it
# uses that file and not lakefile.toml, as far as we know: not tried), so one is rejected and not
# copied. The name is matched in any letter case, and the file system is asked as well: on one that
# ignores case, a Lakefile.lean is a lakefile.lean to Lake.
for f in [
    f
    for f in (sorted(os.listdir(SRC)) if os.path.isdir(SRC) else [])
    if f.casefold() == 'lakefile.lean'
] or (['lakefile.lean'] if os.path.lexists(SRC + '/lakefile.lean') else []):
    lake_code[f] = (
        'the library\'s top directory contains %s: Lake runs a file named '
        'lakefile.lean as a program (on some file systems in any letter '
        'case). The delivered library has none: if you did not put it '
        'there yourself, this is not the delivered library. Rejected '
        'even with --other-lake'
    ) % f
# The reasons that forbid every call of Lake in this run. They also make the step "tree" fail.
# step_build and sh_ test the list themselves, because --only can omit "tree" and a failed step does
# not stop the run.
LAKE_STOP = list(lake_code.values()) + (
    []
    if a.other_lake
    else [
        x
        + (
            ' (the Lake files choose which Lean and which Mathlib are '
            'downloaded, run on your machine and check the library: if you '
            'did not change this file yourself, stop here; to continue '
            'anyway, use --other-lake)'
        )
        for x in lake_other.values()
    ]
)
# If .lake, .lake/packages, a package or .lake/build is a symbolic link, Lake is not called, even
# with --other-lake. (check.py builds in its own copy; .lake/build matters for the reader's own
# calls of Lake.)
PACKAGES_LINKED = [
    p
    for p in ['.lake', '.lake/packages', '.lake/build']
    + [
        '.lake/packages/' + n
        for n in (
            sorted(os.listdir(SRC + '/.lake/packages'))
            if os.path.isdir(SRC + '/.lake/packages')
            else []
        )
    ]
    if os.path.islink(SRC + '/' + p)
]
LAKE_STOP += [
    (
        '%s is a symbolic link. %s To continue, make a fresh copy of the '
        'library and put the packages into it as real directories'
    )
    % (
        plain(p),
        (
            'Lake writes and replaces files wherever the link points.'
            if p == '.lake/build'
            else ('check.py reads the packages only from inside the library.')
        ),
    )
    for p in PACKAGES_LINKED
]
odd_things += LAKE_STOP
# With other Lake files, no last line may look like that of a run with the delivered ones: these
# words come first, whichever steps ran and whatever their results.
LAKE_WORDS = (
    ('The Lake files are not the ones that this check.py expects ' '(%s). ')
    % ', '.join(list(lake_other) + list(lake_code))
    if lake_other or lake_code
    else ''
)

# The single copy of the library: scripts/RULES.txt, "One copy".
lake_folder, UNPRINTABLE = False, []


def unread(e):
    """os.walk calls this for a directory that it cannot list: the step "tree" then fails."""
    odd_things.append('a directory that cannot be read: ' + os.path.relpath(e.filename, SRC))


for r, ds, fs in os.walk(SRC, followlinks=False, onerror=unread):
    rel = os.path.relpath(r, SRC)
    same = {}
    for n in sorted(ds + fs):
        # every name in the directory, whatever its file type
        if n.isprintable():
            same.setdefault(n.casefold(), []).append(n)
        else:
            # It is rejected, and neither copied nor walked. On a screen such a name cannot be told
            # from another, and nothing can import a file that has one.
            UNPRINTABLE.append(plain(os.path.join(rel, n)))
            odd_things.append(
                'a file or directory name contains a character that cannot be printed (written '
                'here as an escape): %s. Rename or remove it' % UNPRINTABLE[-1]
            )
    ds[:] = [d for d in ds if d.isprintable()]
    fs[:] = [f for f in fs if f.isprintable()]
    for v in same.values():
        if len(v) > 1:
            odd_things.append(
                (
                    'names that differ only in letter case: %s, in the directory %s: '
                    'a file system that ignores case (the default on macOS and '
                    'Windows) can hold only one of them'
                )
                % (' | '.join(v), rel)
            )
    for d in list(ds):
        if os.path.islink(r + '/' + d):
            odd_things.append('a directory that is a symbolic link: ' + os.path.join(rel, d))
            ds.remove(d)
    ds[:] = sorted(d for d in ds if not (r == SRC and d == 'scripts'))
    for h in [d for d in ds if d.startswith('.')]:
        if r == SRC and h == '.lake':
            lake_folder = True
            # Lake's directory at the root: after "lake exe cache get" it contains the packages with
            # their sources. It is not searched, and it is not copied here. The build step copies
            # only its packages (lake_project).
            continue
        if any(f.endswith('.lean') for _, _, ff in os.walk(r + '/' + h) for f in ff):
            odd_things.append('a hidden directory with Lean files: ' + os.path.join(rel, h))
    ds[:] = [d for d in ds if not d.startswith('.')]
    for f in sorted(fs):
        if not f.endswith('.lean') or (r == SRC and f == 'lakefile.lean'):
            continue  # a lakefile.lean is not a file of the library
        if os.path.islink(r + '/' + f):
            odd_things.append('a file that is a symbolic link: ' + os.path.join(rel, f))
            continue
        if not os.path.isfile(r + '/' + f):
            odd_things.append(
                'not a regular file (a pipe, a socket, a device): ' + os.path.join(rel, f)
            )
            continue
        put(r + '/' + f, 'tree/' + rel + '/' + f)
try:
    os.mkdir('tree/scripts', dir_fd=OUT_FD)
except FileExistsError:
    pass
for f in DATAFILES:
    # If scripts is itself a symbolic link, nothing below it is copied. (The walk above rejects
    # the link if it points to a directory, and not otherwise.)
    if not os.path.islink(SRC + '/scripts') and there('scripts/' + f):
        put(SRC + '/scripts/' + f, 'tree/scripts/' + f)
        try:
            open(ROOT + '/scripts/' + f, encoding='utf-8').read()
        except UnicodeDecodeError:
            odd_things.append('scripts/%s is not valid UTF-8: it counts as empty' % f)
    elif f == 'RULES.txt':
        odd_things.append('scripts/RULES.txt is missing: the messages of check.py refer to it')
if os.path.isdir(SRC + '/scripts') and any(
    f.endswith('.lean') for f in os.listdir(SRC + '/scripts')
):
    odd_things.append(
        'Lean files in scripts/: they are not part of the library and ' 'nothing may import them'
    )


def data(name):
    """Returns the lines of the copy's file name in scripts/ without their line feeds, leaving out
    blank lines and lines that begin with "#". A file that is absent, cannot be opened or is not
    valid UTF-8 gives the empty list; nothing is raised."""
    try:
        return [
            l.rstrip('\n')
            for l in open(ROOT + '/scripts/' + name, encoding='utf-8')
            if l.strip() and not l.startswith('#')
        ]
    except OSError:
        return []
    except UnicodeDecodeError:
        return []  # the step "tree" fails for it: see where the lists are copied


def files(wip=False):
    """The Lean files of the copy: with wip=True those named *_wip.lean, otherwise all the others.
    Files named *_wip.lean are no part of the library, and no file of the library may import one.
    They are left out of every step; their number is printed."""
    out = []
    for r, ds, fs in os.walk(ROOT):
        ds[:] = sorted(d for d in ds if not (r == ROOT and d == 'scripts'))
        for f in sorted(fs):
            if (
                f.endswith('.lean')
                and f.endswith('_wip.lean') == wip
                and not (r == ROOT and f == 'lakefile.lean')
            ):
                out.append((r + '/' + f)[len(ROOT) + 1 :])  # no call that asks where ROOT lies
    return out


FILES, WIP = files(), files(wip=True)
ODD = [r for r in FILES if not lclib.REL.fullmatch(r)]
# ODD: files whose path is not a module path. No import can name such a file, so it is not part of
# the library. These files are left out, and their number is printed.
FILES = [r for r in FILES if r not in ODD]
# ASK: the asking files, every Lean file below Ask/. A reader runs each of them by the command in
# its head. They are not part of the library: no glob of lakefile.toml reaches them, and no
# file of the library may import one. They are in the digest, and the text rules read them; they
# are not built, not replayed and not audited. scripts/RULES.txt, "Asking files".
ASK = [r for r in FILES if r.startswith('Ask/')]
FILES = [r for r in FILES if not r.startswith('Ask/')]
dg = hashlib.sha256()
for rel in (
    FILES + ASK + ['scripts/' + f for f in DATAFILES if os.path.isfile(ROOT + '/scripts/' + f)]
):
    dg.update(('%s %s\n' % (rel, lclib.sha(open(ROOT + '/' + rel, 'rb').read()))).encode())
DIGEST = dg.hexdigest()


if a.digest:
    print(
        ('%s  %s (the digest of %d Lean files and the data files, as they ' 'are now)%s')
        % (DIGEST, SRC, len(FILES + ASK), SAID)
    )
    if LAKE_WORDS:
        print(LAKE_WORDS.strip() + SAID)
    away(OUT)
    sys.exit(0)


def text(rel):
    """Returns the text of the copy's file rel, decoded as UTF-8; invalid bytes become U+FFFD."""
    # the file's exact characters: Python's text mode treats a lone carriage return as a line break,
    # and Lean does not. Invalid UTF-8 is rejected below (ODD_BYTES); here it becomes U+FFFD, so
    # that no step crashes on it
    return open(ROOT + '/' + rel, 'rb').read().decode('utf-8', 'replace')


# A Lean file of this library may contain printable ASCII, spaces, line feeds and the characters in
# SIGNS, and nothing else; the text "#lang" is rejected too. Why: scripts/RULES.txt, "Characters".
# To use a new character, add it here.
SIGNS = '''
00A7 §  00AB «  00AC ¬  00B0 °  00B1 ±  00B2 ²  00B3 ³  00B5 µ  00B7 ·
00B9 ¹  00BB »  00D7 ×  00E3 ã  00E9 é  00F4 ô  00F6 ö  0105 ą  011D ĝ
0124 Ĥ  0142 ł  015D ŝ  0169 ũ  0237 ȷ  02B3 ʳ  02E2 ˢ  02E3 ˣ  0302 ◌̂
0303 ◌̃  0304 ◌̄  0393 Γ  0394 Δ  0398 Θ  039B Λ  039E Ξ  03A0 Π  03A3 Σ
03A6 Φ  03A8 Ψ  03A9 Ω  03B1 α  03B2 β  03B3 γ  03B4 δ  03B5 ε  03B6 ζ
03B7 η  03B8 θ  03B9 ι  03BA κ  03BB λ  03BC μ  03BD ν  03BE ξ  03BF ο
03C0 π  03C1 ρ  03C2 ς  03C3 σ  03C4 τ  03C6 φ  03C7 χ  03C8 ψ  03C9 ω
03D1 ϑ  03D5 ϕ  03D6 ϖ  03F1 ϱ  03F5 ϵ  1D40 ᵀ  1D50 ᵐ  1D62 ᵢ  1D9C ᶜ
1DA0 ᶠ  1E91 ẑ  2013 –  2016 ‖  2019 ’  2022 •  2026 …  2032 ′  2033 ″
2039 ‹  203A ›  2070 ⁰  2074 ⁴  2078 ⁸  207A ⁺  207B ⁻  207D ⁽  207E ⁾
2080 ₀  2081 ₁  2082 ₂  2083 ₃  2084 ₄  2085 ₅  208A ₊  208B ₋  2090 ₐ
2097 ₗ  2098 ₘ  2113 ℓ  2115 ℕ  211A ℚ  211D ℝ  2124 ℤ  2190 ←  2191 ↑
2192 →  2193 ↓  2194 ↔  21A5 ↥  21A6 ↦  21AA ↪  21D1 ⇑  21D2 ⇒  21D4 ⇔
2200 ∀  2202 ∂  2203 ∃  2205 ∅  2208 ∈  2209 ∉  220F ∏  2211 ∑  2212 −
2217 ∗  2218 ∘  221E ∞  2223 ∣  2227 ∧  2228 ∨  2229 ∩  222A ∪  222B ∫
2243 ≃  2248 ≈  2260 ≠  2261 ≡  2264 ≤  2265 ≥  226B ≫  2282 ⊂  2286 ⊆
2293 ⊓  2295 ⊕  2297 ⊗  229E ⊞  229F ⊟  22A1 ⊡  22A2 ⊢  22A4 ⊤  22A5 ⊥
22C2 ⋂  22C3 ⋃  22C6 ⋆  22C8 ⋈  2308 ⌈  2309 ⌉  230A ⌊  230B ⌋  25B8 ▸
27E8 ⟨  27E9 ⟩  27F9 ⟹  2A06 ⨆  2C7C ⱼ  1D49C 𝒜  1D49E 𝒞  1D4AE 𝒮  1D4DB 𝓛
1D4DD 𝓝  1D509 𝔉
00E1 á  00ED í  02B2 ʲ  1D48 ᵈ  1D65 ᵥ  2014 —  2071 ⁱ  2075 ⁵  209B ₛ
2219 ∙  221A √  2245 ≅  2270 ≰  227C ≼  2287 ⊇  2294 ⊔  22EF ⋯  29F8 ⧸
2A05 ⨅  1D53D 𝔽
201C “  201D ”  2086 ₆  2087 ₇  2088 ₈  2089 ₉  21D0 ⇐  27EB ⟫  27F6 ⟶  27F8 ⟸
27FA ⟺  1D403 𝐃  1D405 𝐅  1D40A 𝐊  1D40B 𝐋  1D40C 𝐌  1D410 𝐐  1D41C 𝐜  1D425 𝐥  1D429 𝐩
1D42B 𝐫  1D42C 𝐬  1D42F 𝐯  1D504 𝔄  1D507 𝔇  1D50F 𝔏  1D6CD 𝛍
210C ℌ  211C ℜ  1D516 𝔖  1D517 𝔗  1D521 𝔡  1D524 𝔤  1D52F 𝔯  1D555 𝕕  1D558 𝕘  1D55A 𝕚
1D563 𝕣  1D564 𝕤  1D568 𝕨  1D56A 𝕪
210D ℍ  212D ℭ  1D413 𝐓  1D41F 𝐟  1D510 𝔐  1D512 𝔒  1D540 𝕀  1D543 𝕃  1D54B 𝕋  1D54E 𝕎
1D54F 𝕏  1D559 𝕙  1D49 ᵉ  2605 ★  03C5 υ
'''  # code point, then the character (a combining mark is shown on a dotted circle)
ALLOWED = (
    set(map(chr, range(32, 127)))
    | {'\n'}
    | {c[-1] for cp, c in re.findall(r'([0-9A-F]{4,5}) (\S+)', SIGNS) if c[-1] == chr(int(cp, 16))}
)
ODD_BYTES = []  # ALLOWED ignores an entry whose character does not match its code point
for rel in FILES + ASK:
    try:
        t = open(ROOT + '/' + rel, 'rb').read().decode('utf-8')
    except UnicodeDecodeError:
        ODD_BYTES.append('%s: it is not valid UTF-8' % rel)
        continue
    ODD_BYTES += [
        (
            '%s:%d: %s, which no Lean file of this library may contain '
            '(scripts/RULES.txt, "Characters")'
        )
        % (
            rel,
            t.count('\n', 0, t.index(c)) + 1,
            'the character U+%04X' % ord(c) if len(c) == 1 else 'the letters ' + c,
        )
        for c in sorted(set(t) - ALLOWED) + ['#lang'] * ('#lang' in t)
    ]


def panic_lines(log):
    """Returns the lines of log (output of Lake, leanchecker or Lean) that report a Lean panic:
    those with PANIC in capitals, and those right before a line "backtrace:". Lean does not
    always print either, so sh_ sets LEAN_ABORT_ON_PANIC; these lines only say why a call failed."""
    lines = [''] + log.split('\n') + ['']
    return [
        l.strip() or '(a panic with an empty message)'
        for l, after in zip(lines, lines[1:])
        if 'PANIC' in l.replace('LEAN_ABORT_ON_PANIC', '') or after.strip() == 'backtrace:'
    ]


def panics(what, codes, log, where):
    """Counts the lines of log that report a panic and, if there are any, prints the first. what
    names the program that wrote log, codes the exit statuses of sh_'s calls, where the file in
    which this run keeps log. If no line reports a panic and Lean aborted all the same in such a
    call, it says what that means."""
    found = panic_lines(log)
    if found:
        print(
            (
                '   PANIC: lines in the output of %s that report a Lean panic: '
                '%d, so this step counts as failed. The first: %s (all of them: '
                '%s/%s)'
            )
            % (what, len(found), found[0][:300], OUT, where)
        )
    elif {134, -6} & set(codes) or 'exited with code 134' in log:
        print(
            (
                '   Lean aborted (exit status 134) in %s. check.py runs it with '
                'LEAN_ABORT_ON_PANIC=1, so this is most likely a panic; see %s/%s'
            )
            % (what, OUT, where)
        )
    return len(found)


# Memory that check.py asks for before a step, in GiB. These are floors, not what a step needs: the
# largest process can hold more, and so can the replay's jobs together (scripts/RULES.txt, "The
# build"). 2 for each additional parallel replay job is a rule of thumb, not measured
BUILD_GIB, REPLAY_GIB, REPLAY_MORE_GIB = 21, 21, 2
# The bound on parallel work. To compile a module of ShapeLines/ takes a heavy Lean process. Lake,
# left alone, starts about one process per core, which can run a machine with many cores out of
# memory (reckoned, not run), so the script always hands "lake build" a bound: the caller's
# LEAN_NUM_THREADS, or else the number that lean_bound works out. The two numbers below are that
# rule of thumb. HEAVIEST_GIB is 49.1 GiB rounded up: the greatest resident memory of one process in
# one build of ShapeLines/ at LEAN_NUM_THREADS=16, by samples taken every five seconds
# (ShapeLines/README.md, "How to build, and what it costs", the table). HEAVY_MORE_GIB is the room
# for each further process, from one call "lake build ShapeLines.FirstChainRuns" at
# LEAN_NUM_THREADS=20, of 310 modules in 24 minutes on a machine with 96 cores, which that page does
# not tell: at two looks during the call the machine had 234 and 255 GiB in use, and 30 before the
# build of which it was a part began; 225 / 20 is about 11, rounded up. That page tells the same
# call at LEAN_NUM_THREADS=48: the most that its processes held together is close to the 614 GiB
# that the rule counts for 48 processes (50 + 47 x 12). So the rule leaves little room, or none.
HEAVIEST_GIB, HEAVY_MORE_GIB = 50, 12
# The room for the first replay by the other call and for each further one, unless --wide-jobs gives
# their number. A rule of thumb, not a measured need. The 50 is taken over from the build. The 40
# GiB are 39.4 GiB rounded up: what one process of this call was seen to hold of its own, at 28 at a
# time, with LEAN_NUM_THREADS=8 and with 1, which this script sets. At eight threads 72 at a time,
# and 40 at a time, overran a limit of 800 GiB. The trials: lean/CHECKING.md.
WIDE_FIRST_GIB, WIDE_MORE_GIB = 50, 40
# The most replay jobs that run in parallel without --jobs. Chosen from a few timed runs (on 128
# hardware threads, 48 jobs were faster than 128); not a measured optimum.
REPLAY_MOST = 48
# The audit can run in parts, SIDE of them in parallel: 5 GiB are counted for each, plus 1 for the
# parent process. (In an audit that was made the library needed no parts: one process, which held
# more than the 21 counted here.)
SIDE = max(1, min(4, a.jobs or 4))
AUDIT_GIB = max(7, 5 * SIDE + 1)
# A limit on the address space of each audit process (the parent and each part), not on memory in
# use and not on their total: Lean maps its files and reserves a stack per thread. Seen over 29,905
# modules, 901 of them in AtFullSide/: in a whole run of this script's steps the audit failed under
# a limit of 48 GiB, its process ending with "failed to read file" while it imported; the same audit
# file, run by hand, went through under 96 GiB, with a peak of 53.0 GiB of address space, at
# LEAN_NUM_THREADS=24 on 84 cores. A process that exceeds the limit exits, and the audit fails; with
# many more threads, or a larger library, raise it.
AUDIT_CAP = 96 * 2**30
# The modules of two libraries go through the kernel replay by another call than the rest (the rule
# is below, behind the table). Why there is another call, shown at one module: leanchecker runs each
# module's replay as a task, on a thread of Lean's runtime with that runtime's own stack, and has no
# option for a larger one; a larger limit in the shell changed nothing (tried at 256 MiB and 1 GiB).
# In AtFullSide/Layout/TieRfl.lean the kernel compares two lists of 224,975 characters (the constant
# Johnson.Unfolds.Layout.lay_chars). At Lean's default stack it stops there with "deep recursion
# detected", when the file is compiled and when leanchecker replays it. lakefile.toml gives Lean a
# thread stack of 128 MiB (--tstack=131072) to compile that directory. For the replay of that module
# check.py hands Lean four lines (WIDE_TEXT) on its standard input. They import the toolchain's own
# module LeanChecker and call replayFromImports, the function that leanchecker, called as here
# without --fresh, calls for each module. Lean runs them with the same --tstack. The module is not
# left out.
# The table holds that one name, and pin_shape stops the run if it holds none or more than one. It
# does not say which modules go by the other call, only that this one must be there. What the other
# call does not do that leanchecker does: scripts/RULES.txt, "One module is replayed by another
# call".
# PINS: BEGIN
WIDE_REPLAY = ['AtFullSide.Layout.TieRfl']
# PINS: END
pin_shape('WIDE_REPLAY', WIDE_REPLAY)
WIDE_STACK_KB = 131072
# The rule: every module of a Lake library that lakefile.toml compiles at a larger stack goes by
# that other call too, one process a module, at that very stack: leanchecker replays none of them.
# Which libraries these are is read from lakefile.toml (wide_libraries); the delivered file has two,
# AtFullSide and ShapeLines. In a whole run in which AtFullSide/ had 901 modules and leanchecker was
# given all of them but the table's one, and in a second pass over what that run had left, 22 more
# ended with "deep recursion detected"; none did in the main library. Of ShapeLines/ nobody has
# tried which modules would pass at leanchecker's stack, and one needs more than 128 MiB even to
# compile.
# The rule does not go by a table of the modules that failed: such a table is true of one state of
# the files, a new failure shows only at the end of a whole run, and a run names only the first
# failure of each job. Nor does the script try leanchecker first and the other call after a stack
# failure: leanchecker gives one exit status for a list of names, and a list of one name costs a
# walk of the whole search path. The main library stays with leanchecker, and WIDE_REPLAY holds one
# name, with its pin: the replay fails if that module is gone.
# The two calls compared, item by item as in scripts/RULES.txt, "One module is replayed by another
# call". The same: replayFromImports is the function that leanchecker calls for each module. It
# imports the module's imports as they lie compiled and sends the module's own constants through the
# kernel again. Not the same:
# - Lean's #eval runs the function, where in leanchecker it is part of a compiled program.
# - It runs inside "lean", where --tstack sets the stack.
# - The name means that one module, where leanchecker takes a name as a prefix.
# - The search path is the one that "lean" sets up from LEAN_PATH.
# - The report is this script's closing line, where leanchecker prints "replaying" and the name.
# - "import LeanChecker" loads Lean's and Lake's own modules into the process that runs the four
#   lines. The environment that is replayed into is made anew from the module's imports, as in
#   leanchecker.
# - Where the compiled files are symbolic links, leanchecker found none of them, and the other call
#   read the link. This script's build makes real files.
# Ways to be deceived: a module LeanChecker of the library's own would be found first (the replay
# fails on one; a package's is not looked for). A compiled LeanChecker.olean that code running
# during the build laid on the search path would be taken unseen: that the four lines go over
# standard input does not close that road. Whether leanchecker is open to the compiled file was not
# looked at.
# Not looked at: whether #eval runs the function in the interpreter or as linked code; whether the
# two programs hold the same kernel (both come from one toolchain); whether "lean" runs initialisers
# of the modules that it imports where leanchecker does not (the step "words" and the audit reject
# initialisers in this library).
# Not tried: whether either call refuses a compiled file that has been tampered with; whether 128
# MiB suffice for TieRfl on another system than Linux.


def wide_libraries(toml):
    """From the text of lakefile.toml: (directory, KiB) for each library that it has Lean compile at
    a larger thread stack. So a further such library needs no change of code, only its sum in
    WIDE_SUMS. This does not read TOML.
    It takes the lines as they are and knows one form, the delivered file's: below a line
    [[lean_lib]], and before the next line that opens a table, the three whole lines
        name = "Name"
        globs = ["Name.+"]
        moreLeanArgs = ["--tstack=N"]
    each once. A line whose first sign is '#' is a remark and is passed over. If the letters
    "tstack" stand in any other line, in any other form, under any other key or in any other kind
    of table, the run stops: this script could then not tell which modules are compiled at which
    stack. It also stops if the letters "LeanArgs" stand in any line but these (a second option
    could lower the stack again), at a backslash in any line that is no remark (a key in quotation
    marks could spell these letters with an escape), and at three quotation marks in a row anywhere
    in the file (a string of several lines could hold lines that look like a table)."""
    tables = [('', [])]
    exact = r'moreLeanArgs = \["--tstack=[1-9][0-9]*"\]'
    odd = [
        l
        for l in toml.split('\n')
        if not l.lstrip().startswith('#')
        and (('LeanArgs' in l and not re.fullmatch(exact, l)) or '\\' in l)
    ]
    if odd or '"""' in toml or "'''" in toml:
        print(
            'check.py: lakefile.toml has a string of several lines, or gives Lean arguments in a '
            'line that this script does not read (it reads the whole line moreLeanArgs = '
            '["--tstack=N"]), or has a backslash outside a remark: %s. Nothing was checked.'
            % ' '.join(odd)[:200],
            file=sys.stderr,
        )
        sys.exit(2)
    for l in toml.split('\n'):
        if l.lstrip().startswith('#'):
            continue
        if re.fullmatch(r'\s*\[.*\]\s*', l) and '=' not in l:
            tables.append((l, []))
        else:
            tables[-1][1].append(l)
    out = []
    for head, lines in tables:
        if not [l for l in [head] + lines if 'tstack' in l]:
            continue
        stack = [re.fullmatch(r'moreLeanArgs = \["--tstack=([1-9][0-9]*)"\]', l) for l in lines]
        stack = [m.group(1) for m in stack if m]
        name = [re.fullmatch(r'name = "([A-Za-z][A-Za-z0-9_]*)"', l) for l in lines]
        name = [m.group(1) for m in name if m]
        if (
            head != '[[lean_lib]]'
            or len(stack) != 1
            or len([l for l in lines if 'tstack' in l]) != 1
            or len(name) != 1
            or len([l for l in lines if re.match(r'\s*name\b', l)]) != 1
            or lines.count('globs = ["%s.+"]' % name[0]) != 1
            or len([l for l in lines if re.match(r'\s*(globs|roots|srcDir)\b', l)]) != 1
        ):
            print(
                'check.py: lakefile.toml sets a thread stack in a form that this script does not '
                'read (it reads, below a line [[lean_lib]], the whole lines name = "Name", globs = '
                '["Name.+"] and moreLeanArgs = ["--tstack=N"], each once): %s %s. Nothing was '
                'checked.' % (head, ' '.join(name)),
                file=sys.stderr,
            )
            sys.exit(2)
        out.append((name[0], int(stack[0])))
    return tuple(out)


# Read from the copy of lakefile.toml whose sha256 is compared above (LAKE_FILES). Where that file
# is absent, a link or no regular file, the step "tree" says so and fails; nothing is read here.
try:
    WIDE_LIBRARIES = (
        ()
        if 'lakefile.toml' in lake_code
        else wide_libraries(open(ROOT + '/lakefile.toml', encoding='utf-8').read())
    )
except UnicodeDecodeError:
    print('check.py: lakefile.toml is not UTF-8 text. Nothing was checked.', file=sys.stderr)
    sys.exit(2)
WIDE_NAMES = 'replay-other-call.txt'  # in the scratch directory, with the logs
WIDE_TEXT = (
    'import LeanChecker\n'
    '#eval show IO Unit from do\n'
    '  replayFromImports `%s\n'
    '  IO.println "REPLAYED %s %s"\n'
)


def free_gib():
    """Available memory in GiB: the smaller of MemAvailable and what the cgroup limit leaves. None
    if neither can be read (not Linux)."""
    got = []
    try:
        got.append(
            int(re.search(r'MemAvailable:\s+(\d+) kB', open('/proc/meminfo').read()).group(1))
            * 1024
        )
    except (OSError, AttributeError):
        pass
    try:
        got.append(
            int(open('/sys/fs/cgroup/memory.max').read())
            - int(open('/sys/fs/cgroup/memory.current').read())
            + sum(
                int(l.split()[1])
                for l in open('/sys/fs/cgroup/memory.stat')
                if l.split()[0] in ('inactive_file', 'active_file')
            )
        )  # the cgroup counts the page cache as used; it is reclaimed on demand
    except (OSError, ValueError):
        pass  # no such file, or "max" (no limit)
    return min(got) / 2**30 if got else None


def replay_jobs(asked, free, cores):
    """Number of parallel replay jobs: the number given by --jobs; otherwise one, plus one for each
    REPLAY_MORE_GIB available beyond REPLAY_GIB, at most one per core and at most REPLAY_MOST. If
    the available memory is not known (free is None) and --jobs is not given: one per core, at most
    REPLAY_MOST."""
    return (
        asked
        if asked > 0
        else (
            min(cores, REPLAY_MOST)
            if free is None
            else max(1, min(cores, REPLAY_MOST, 1 + int((free - REPLAY_GIB) / REPLAY_MORE_GIB)))
        )
    )


def lean_bound(said, free, cores):
    """How many heavy Lean processes may run at a time, and where that number comes from. said is
    the caller's LEAN_NUM_THREADS: a whole number above 0 is taken as it stands, even if the memory
    looks too small for it, because the caller may know better. Otherwise: one, plus one for each
    HEAVY_MORE_GIB available beyond HEAVIEST_GIB, at most one per core. If the available memory is
    not known (free is None): one."""
    if re.fullmatch('[1-9][0-9]*', said or ''):
        return int(said), "the caller's LEAN_NUM_THREADS"
    n = max(1, min(cores, 1 + int(((free or 0) - HEAVIEST_GIB) / HEAVY_MORE_GIB)))
    return n, (
        'worked out from the free memory, which could not be read'
        if free is None
        else 'worked out from %.0f GiB of free memory and %d cores' % (free, cores)
    )


def wide_bound(asked, side, whence, free):
    """How many modules go through the other call at a time, and where that number comes from.
    asked is --wide-jobs: a number above 0 is taken as it stands. Otherwise side, the bound that
    holds for "lake build" (and --jobs, if lower), whose origin is whence, but no more than one,
    plus one for each WIDE_MORE_GIB available beyond WIDE_FIRST_GIB: also where the caller stated
    that bound, which is meant for the build. If the available memory is not known (free is
    None): side."""
    if asked > 0:
        return asked, '--wide-jobs'
    if free is None:
        return side, whence + ', and --jobs'
    n = max(1, 1 + int((free - WIDE_FIRST_GIB) / WIDE_MORE_GIB))
    return (
        (side, whence + ', and --jobs')
        if side <= n
        else (n, 'worked out from %.0f GiB of free memory, %d GiB for each' % (free, WIDE_MORE_GIB))
    )


def wide_modules(mods):
    """The modules of mods that the kernel replay takes by the other call, each with its stack in
    KiB: the one name of WIDE_REPLAY, whether or not it is in mods (the replay's verdict fails if it
    is not), then every other module below a library of WIDE_LIBRARIES. This is the one place that
    says which modules leave leanchecker."""
    return [(m, WIDE_STACK_KB) for m in WIDE_REPLAY] + [
        (m, kb)
        for lib, kb in WIDE_LIBRARIES
        for m in mods
        if m.startswith(lib + '.') and m not in WIDE_REPLAY
    ]


# Which modules leave leanchecker is pinned: for each library of WIDE_LIBRARIES, the sha256 of its
# modules in order, each on a line with its stack ("Name --tstack=N"). So a further library, a
# module moved into one of these directories, or another stack costs a change of this value, which
# is read, and not only a line of lakefile.toml with its sum.
# PINS: BEGIN
WIDE_SUMS = {
    'AtFullSide': '871046367868aebe46f2cf445d3a7973667064bb93c953a9a531c38e72219b79',
    'ShapeLines': '953b15c64a5c7634d0a1c039fe8dd60a0d6cd128822e9e5964f2d3f9e46da9ff',
}
# PINS: END
pin_shape('WIDE_SUMS', WIDE_SUMS)


def wide_pinned(mods):
    """Returns (whether the modules of mods that go by the other call are the pinned ones, a line
    that says so). The libraries must be those of WIDE_SUMS, no more and no fewer."""
    now = {}
    for lib, _ in WIDE_LIBRARIES:
        mine = [x for x in wide_modules(mods) if x[0].startswith(lib + '.')]
        rows = sorted('%s --tstack=%d\n' % x for x in mine)
        now[lib] = (len(rows), lclib.sha(''.join(rows).encode('utf-8')))
    gone = sorted(set(WIDE_SUMS) - set(now))
    off = ['%s/ is pinned and is no such library' % x for x in gone] + [
        '%s/ would now have the sum %s' % (x, now[x][1])
        for x in sorted(now)
        if WIDE_SUMS.get(x) != now[x][1]
    ]
    return not off, (
        'the modules that the kernel replay takes by another call than leanchecker: %s; %s'
        % (
            ', '.join('%s/: %d' % (x, now[x][0]) for x in sorted(now)) or 'none',
            'they are the pinned ones (WIDE_SUMS)'
            if not off
            else 'NOT the pinned ones (WIDE_SUMS; if the change is deliberate, read it): '
            + '; '.join(off),
        )
    )


def short_of(what, gib):
    """True, after printing a line, if less memory is available than the step described by what
    needs (gib GiB). If the available memory cannot be read, it prints a line and returns False."""
    free = free_gib()
    if free is None:
        print(
            ('   cannot read how much memory is free on this system; for %s this script ' 'asks %d GiB free, and more has been seen')
            % (what, gib)
        )
    elif free < gib:
        print(
            ('   TOO LITTLE MEMORY: for %s this script asks %d GiB free, and more has been seen; %.1f GiB are ' 'free')
            % (what, gib, free)
        )
    return free is not None and free < gib


def sh_(cmd, cwd, log, env=None, cap=None, said=None):
    """Runs cmd in cwd, writes its output to the file log in OUT and returns (exit status, output).
    cap, if given, limits the address space in bytes; said, if given, is the text handed to the
    process on its standard input. Used for every call of Lake, and for nothing
    else. Sets LEAN_ABORT_ON_PANIC=1, so that Lean aborts at its first panic (exit status 134;
    "lake build" then exits with 1)."""
    # A second safeguard: step_build already returns when LAKE_STOP is set. The second test and the
    # third ask what Lake would find in the copy now (the third: whether each of the three files is
    # a regular file, not what it holds). None protects against hostile code that ran in an earlier
    # call of Lake.
    if LAKE_STOP or os.path.lexists(ROOT + '/lakefile.lean'):
        raise RuntimeError(
            'check.py: Lake must not be called: '
            + (
                '; '.join(LAKE_STOP)
                or ('the copy contains a lakefile.lean, which check.py did not put ' 'there')
            )
        )
    gone = [
        f
        for f in LAKE_FILES
        if os.path.islink(ROOT + '/' + f) or not os.path.isfile(ROOT + '/' + f)
    ]
    if gone:
        raise RuntimeError(
            'check.py: Lake must not be called: the copy no longer has %s as a regular file. '
            'Something changed the copy during this run, which stops here. The copy stays in %s'
            % (', '.join(gone), OUT)
        )
    if cap:
        hard = resource.getrlimit(resource.RLIMIT_AS)[1]
        # a lower hard limit set by the caller is kept
        cap = cap if hard == resource.RLIM_INFINITY else min(cap, hard)
    # An aborted process can hold 20 GiB: the soft limit on core files is set to 0, for check.py and
    # what it starts.
    resource.setrlimit(resource.RLIMIT_CORE, (0, resource.getrlimit(resource.RLIMIT_CORE)[1]))
    p = subprocess.run(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        input=said,
        text=True,
        errors='backslashreplace',  # a byte that is not UTF-8 must not end the run in a traceback
        env=dict(os.environ if env is None else env, LEAN_ABORT_ON_PANIC='1'),
        preexec_fn=(lambda: resource.setrlimit(resource.RLIMIT_AS, (cap, cap))) if cap else None,
    )
    open(fresh(log), 'w', errors='backslashreplace').write(p.stdout)
    return p.returncode, p.stdout


def packages_fault():
    """Returns the reason why .lake/packages cannot be used, or None. It is called before the
    packages are copied and before Lake is called. It makes one pass, which follows links as the
    copy will."""
    top, seen = SRC + '/.lake/packages', set()
    source, built = (
        set(),
        set(),
    )  # Mathlib's modules: those with a source file, those with a compiled file
    size = 0
    if not os.path.isdir(top):
        return (
            'the library has no directory .lake/packages: run "lake exe '
            'cache get" in the library first'
        )
    for r, ds, fs in os.walk(top, followlinks=True):
        if os.path.realpath(r) in seen:
            return (
                'below .lake/packages the directory %s is reached a second time, '
                'through a link, so it cannot be copied as it is'
            ) % os.path.relpath(r, top)
        seen.add(os.path.realpath(r))
        # the package that contains r
        home = os.path.realpath(top + '/' + os.path.relpath(r, top).split('/')[0])
        for n in ds + fs:
            p = r + '/' + n
            q = os.path.relpath(p, top)
            is_file = os.path.isfile(p)
            if not os.path.exists(p):
                return 'below .lake/packages the link %s points to nothing' % q
            if os.path.islink(p) and not (os.path.realpath(p) + '/').startswith(home + '/'):
                return 'below .lake/packages the link %s points outside its package' % q
            if is_file and q.startswith('mathlib/Mathlib/') and q.endswith('.lean'):
                source.add(q[len('mathlib/') : -len('.lean')])
            if (
                is_file
                and q.startswith('mathlib/.lake/build/lib/lean/Mathlib/')
                and q.endswith('.olean')
            ):
                built.add(q[len('mathlib/.lake/build/lib/lean/') : -len('.olean')])
            if is_file:
                size += os.path.getsize(p)
    free = shutil.disk_usage('.').free  # on the file system of the scratch directory
    if size * 1.1 > free:
        return (
            'the copy of .lake/packages needs %.1f GiB, and the disk of the '
            'scratch directory (%s) has %.1f GiB free, which is too little '
            '(check.py asks for a tenth more than the copy). Nothing was '
            'copied'
        ) % (
            size / 2**30,
            OUT,
            free / 2**30,
        )  # the build's output comes on top and is not bounded here
    # "lake exe cache get" can be interrupted, or exit with status 0 without downloading anything
    # ("Downloaded: 0"). Lake would then fetch the missing packages and compile Mathlib itself:
    # hours, and many GB
    try:
        named = [
            p['name']
            for p in json.load(open(ROOT + '/lake-manifest.json', encoding='utf-8'))['packages']
        ]
    except (OSError, ValueError, KeyError, TypeError):
        named = []
    gone = [n for n in named if not os.path.isdir(top + '/' + n)] + (
        ['mathlib (it contains no source file)']
        if 'mathlib' in named and os.path.isdir(top + '/mathlib') and not source
        else []
    )
    if gone:
        return (
            'lake-manifest.json names packages that are not below '
            '.lake/packages: %s. "lake exe cache get" did not finish in the '
            'library, and Lake would download them itself. Nothing was copied'
        ) % ', '.join(gone)
    if source - built:
        return (
            'the packages are there, but of Mathlib\'s %d source files %d '
            'have no compiled file: "lake exe cache get" did not download '
            'them, and Lake would compile them itself, which takes hours and '
            'many GB. Nothing was copied'
        ) % (len(source), len(source - built))
    return None


def lake_project(dst):
    """Adds a real copy of the library's packages to the copy dst and makes it writable, so that
    whatever Lake writes or removes under .lake/packages stays inside the scratch directory. A link
    to a file of the same package becomes a file. Modification times are kept, so that Lake finds
    the packages up to date."""
    os.makedirs(dst + '/.lake', exist_ok=True)
    if not os.path.lexists(dst + '/.lake/packages'):
        shutil.copytree(SRC + '/.lake/packages', dst + '/.lake/packages', symlinks=False)
        # the original may be read-only; Lake must be able to write in the copy
        for _, _, fs, fd in os.fwalk(dst + '/.lake/packages', dir_fd=OUT_FD):
            os.fchmod(fd, os.fstat(fd).st_mode | 0o700)
            for n in fs:
                try:
                    f = os.open(n, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
                except OSError:
                    continue  # a file that its owner may not read keeps its mode
                os.fchmod(f, os.fstat(f).st_mode | 0o200)
                os.close(f)


# Plain "lake build" builds the default targets of lakefile.toml, and ShapeLines is none. Its files
# that AtFullSide reaches by imports get built all the same, but not the three in THIRD_ONLY, which
# neither default target reaches. So the build names all three libraries, in one call.
# The test on compiled files has no list of excused files: every Lean file must have its compiled
# file.
BUILD_TARGETS = ['Library', 'AtFullSide', 'ShapeLines']
# The files that only the target ShapeLines reaches (ShapeLines/README.md, "How to build"). A file
# missing from the copy fails nothing by itself, so a copy that has lost one of these would pass in
# silence: the verdict on the build fails if one is not in the copy. Two of them are controls; the
# third, LastRunAtBorder358.lean, holds a fact and no control.
THIRD_ONLY = [
    'ShapeLines/Equations/EquationTestControls.lean',
    'ShapeLines/LastChain/LastRunAtBorder358.lean',
    'ShapeLines/LastChain/LastRunControls.lean',
]
# REPLAY_CALL: a directory's name is handed to leanchecker if at most this many modules lie below
# it (a module that is also a directory brings all that lies below it, however many). REPLAY_PACK:
# names that bring fewer modules are put together into one call up to this load, where a name counts
# as the modules that it brings and three more, for its search. Both are set by reckoning from one
# timed trial (48 calls with one directory's name each); not a measured optimum.
REPLAY_CALL = 600
REPLAY_PACK = 150


def replay_lists(mods):
    """Splits mods into argument lists for leanchecker, one list per process. Returns (the lists,
    the modules left out). leanchecker takes a name as a prefix, and for every name that it is given
    it first looks at every compiled file on the search path, which takes far longer than a module's
    replay (scripts/RULES.txt, "The kernel replay's names"). So it is given few names: a directory's
    name stands for all modules below it, if these are at most REPLAY_CALL and none of them must
    stay out. Must stay out: the modules of wide_modules, which the caller has taken out of mods,
    and a module that is also a directory's name and contains only import lines (left out).
    Such a module with other contents is named itself, and brings the modules under its name. What
    was replayed is read from leanchecker's own print, not from these lists: the verdict compares it
    with the compiled modules, name for name. The longest lists come first."""
    have = set(mods)
    folder = [m for m in mods if any(x.startswith(m + '.') for x in mods)]

    def only_imports(m):
        t = text(lclib.rel_of(m))
        # Applied to the raw text: a module that also contains a comment gets a separate process.
        # (If code_of blanked the comments first, code that code_of mistakes for a comment would
        # escape the replay.)
        body = re.sub(r'(?m)^\s*(public\s+|meta\s+)*import\s+(all\s+)?[A-Za-z0-9_.]+\s*$', '', t)
        try:
            return bool(lclib.imports_of(t)) and not body.strip()
        except ValueError:
            return False  # a header that cannot be read: the module is replayed

    skip = {m for m in folder if only_imports(m)}
    # below[p]: the modules to replay whose name is p or begins with p and a dot; out: every prefix
    # of a name that must stay out, so that no such prefix is handed to leanchecker
    below, kids, out = {}, {}, set()
    for m in list(skip) + list(WIDE_REPLAY):
        p = m.split('.')
        out.update('.'.join(p[:i]) for i in range(1, len(p) + 1))
    for m in mods:
        if m in skip:
            continue
        p = m.split('.')
        for i in range(1, len(p) + 1):
            below.setdefault('.'.join(p[:i]), []).append(m)
            if i < len(p):
                kids.setdefault('.'.join(p[:i]), set()).add('.'.join(p[: i + 1]))
    names = []  # (the name to hand over, how many modules it brings)

    def walk(p):
        if p not in out and (len(below[p]) <= REPLAY_CALL or p in have):
            names.append((p, len(below[p])))
        elif p in have and p not in skip:
            # a module above a name that must stay out: leanchecker would take that one too. It is
            # named all the same, and the replay's verdict then fails: for WIDE_REPLAY the caller
            # says why; for a module of import lines alone the line "REPLAYED BUT NOT EXPECTED"
            # names it
            names.append((p, len(below[p])))
        else:
            for k in sorted(kids.get(p, ())):
                walk(k)

    for p in sorted({m.split('.')[0] for m in below}):
        walk(p)
    lists, now, load = [], [], 0
    for p, n in sorted(names, key=lambda x: (-x[1], x[0])):
        w = n + 3
        if now and load + w > REPLAY_PACK:
            lists.append(now)
            now, load = [], 0
        now.append(p)
        load += w
    if now:
        lists.append(now)
    return lists, skip


def panic_control():
    """A control on this machine's Lean and Lake, before any file of the library is compiled: a
    one-line file that panics, run as the audit is run. True if Lean stopped there: the call failed,
    its output reports the panic, and the default value 0 does not follow. The verdicts on build,
    replay and audit assume that."""
    open(fresh('PanicControl.lean'), 'w').write('#eval (panic! "control" : Nat)\n')
    rc, o = sh_(['lake', 'env', 'lean', '../PanicControl.lean'], ROOT, 'panic-control.log')
    stopped = rc != 0 and bool(panic_lines(o)) and '0' not in o.split('\n')
    if not stopped:
        print(
            (
                '   THE CONTROL FAILED: a one-line file that panics must make '
                'Lean stop and report the panic; here "lake env lean" ended with '
                'exit status %d, with %d lines that report a panic, and the '
                'default value %s. On this machine a panic in the build, the '
                'replay or the audit could go unnoticed. Log: '
                '%s/panic-control.log'
            )
            % (
                rc,
                len(panic_lines(o)),
                'followed' if '0' in o.split('\n') else 'did not follow',
                OUT,
            )
        )
    return stopped


def lake_build(named):
    """Runs "lake build" from scratch in the copy, on all of BUILD_TARGETS, at a bound on parallel
    work. Returns (exit status, the files of named that it did not build, the number of messages
    about sorry, the number of lines that report a panic)."""
    lake_project(ROOT)
    for r in WIP + ODD + ASK:
        # not part of the library, but a lakefile's globs would build them all the same (ASK: no
        # glob reaches them; without them an import of one fails in the build too)
        os.unlink('tree/' + r, dir_fd=OUT_FD)
    threads, whence = lean_bound(
        os.environ.get('LEAN_NUM_THREADS'), free_gib(), os.cpu_count() or 4
    )
    print(
        '   "lake build" on %s, with LEAN_NUM_THREADS=%d (%s)'
        % (' '.join(BUILD_TARGETS), threads, whence),
        flush=True,
    )
    counts['Lean processes at a time in "lake build", at most (%s)' % whence] = threads
    rc, o = sh_(
        ['lake', 'build'] + BUILD_TARGETS,
        ROOT,
        'build.log',
        dict(os.environ, LEAN_NUM_THREADS=str(threads)),
    )
    lib = ROOT + '/.lake/build/lib/lean/'
    missing = [r for r in named if not os.path.isfile(lib + r[:-5] + '.olean')]
    for l in o.split('\n'):
        if l.startswith('error') or re.match(r'\s*- ', l):
            print('   ' + l[:300])
    sorries = len(re.findall(r"declaration uses \x60?'?sorry", o))
    return rc, missing, sorries, panics('"lake build"', [rc], o, 'build.log')


def replay_and_audit(mods, nonce):
    """Replay and audit. Returns (modules replayed by leanchecker, modules with imports only, replay
    ok, the audit's exit code, the audit's lines, the numbers of lines that report a panic in the
    replay's and in the audit's output, the modules of wide_modules that the other call replayed).
    """
    heavy = wide_modules(mods)
    lists, skip = replay_lists([m for m in mods if m not in {x for x, _ in heavy}])
    env = dict(os.environ, LEAN_NUM_THREADS='1')

    def one(il):
        return sh_(['lake', 'env', 'leanchecker', '-v'] + il[1], ROOT, 'replay.%d.log' % il[0], env)

    jobs = replay_jobs(a.jobs, free_gib(), os.cpu_count() or 4)
    print(
        (
            '   the kernel replay: %d jobs in parallel (without --jobs: one, and one '
            'more for each 2 GiB free beyond 21, at most one per core and at '
            'most %d: a rule of thumb, not what the jobs need)'
        )
        % (jobs, REPLAY_MOST),
        flush=True,
    )
    # The other call goes first: a failure in it then shows before leanchecker's long run, not
    # behind it. Its processes run side by side, or the two libraries' modules would take the whole
    # sum of their times. Their number is --wide-jobs, if that is given. Otherwise they keep to the
    # same bound as the build, to the number of replay jobs if that is lower, and to a rule of thumb
    # of their own (wide_bound): what such a process was seen to need is told in scripts/RULES.txt,
    # "What the other call needs". They end before leanchecker's jobs start, so the two groups of
    # processes never run at once.
    side, whence = lean_bound(os.environ.get('LEAN_NUM_THREADS'), free_gib(), os.cpu_count() or 4)
    side = min(side, jobs)
    side, whence = wide_bound(a.wide_jobs, side, whence, free_gib())
    counts['replays by the other call at a time, at most (%s)' % whence] = side
    # The whole list of names, for whoever wants to see what left leanchecker, stays with the logs.
    open(fresh(WIDE_NAMES), 'w').write(''.join('%s --tstack=%d\n' % x for x in heavy))
    for m in WIDE_REPLAY:
        print(
            (
                '   the kernel replay: %s goes by another call, "lake env lean --tstack=%d '
                '--stdin" on four lines that call replayFromImports, the function that leanchecker '
                'calls for each module: at leanchecker\'s own stack the kernel stops at one '
                'constant of that module with "deep recursion detected". What this call does not '
                'do that leanchecker does: scripts/RULES.txt, "One module is replayed by another '
                'call"'
            )
            % (m, WIDE_STACK_KB),
            flush=True,
        )
    for lib, kb in WIDE_LIBRARIES:
        below = len([m for m, _ in heavy if m.startswith(lib + '.')])
        print(
            '   the kernel replay: every module of %s/, %d in all, goes by the other call too, '
            'with --tstack=%d, at most %d at a time; leanchecker replays none of them; all names: '
            '%s/%s' % (lib, below, kb, side, OUT, WIDE_NAMES),
            flush=True,
        )
    named_to_checker = [x for x in mods if x not in skip and x not in {y for y, _ in heavy}]

    def wide_one(item):
        """Replays one module by the other call. Returns (the module's name if it passed, else
        None; the call's (status, output), or None if no call was made)."""
        k, (m, stack) = item
        # leanchecker takes a name as a prefix, and "import LeanChecker" is found by its name. A
        # module that itself goes by the other call is never handed to leanchecker.
        above = [x for x in named_to_checker if m.startswith(x + '.')]
        why = (
            'it is no compiled module of this library'
            if m not in mods
            else 'leanchecker would take it too, under the name %s' % above[0]
            if above
            else 'this library has a module LeanChecker of its own'
            if any(x.split('.')[0] == 'LeanChecker' for x in mods)
            else ''
        )
        if why:
            print(
                '   REPLAY FAILED for %s, which goes by the other call: %s' % (m, why), flush=True
            )
            return None, None
        # The four lines go over standard input: no file of them lies where a process that an
        # earlier call left behind could rewrite it between its writing and its reading.
        r = sh_(
            ['lake', 'env', 'lean', '--tstack=%d' % stack, '--stdin'],
            ROOT,
            'replay.wide.%d.log' % k,
            env,
            said=WIDE_TEXT % (m, m, nonce),
        )
        # the closing line is printed only behind the call, and bears this run's own word
        closed = r[1].split('\n').count('REPLAYED %s %s' % (m, nonce)) == 1
        if r[0] == 0 and closed:
            return m, r
        print(
            '   REPLAY FAILED (exit %d; the closing line is %s) for: %s: %s'
            % (r[0], 'there' if closed else 'NOT there', m, r[1].strip().split('\n')[-1][:200]),
            flush=True,
        )
        return None, r

    with concurrent.futures.ThreadPoolExecutor(side) as ex:
        done = list(ex.map(wide_one, enumerate(heavy)))
    wide = {m for m, _ in done if m}
    first = [r for _, r in done if r]
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        rs = list(ex.map(one, enumerate(lists)))
    # leanchecker prints "replaying M" before it replays M. A job that did not end with status 0
    # stopped inside the last module that it named, so that one does not count as replayed. Its
    # message of failure can stand behind a further "replaying ", so the last name that is a module
    # is taken, not the last word found; a word that is no module stays and is reported below.
    seen, known = set(), set(mods)
    for c, t in rs:
        named = re.findall(r'(?m)^replaying (\S+)', t)
        real = [i for i, m in enumerate(named) if m in known]
        if c and real:
            del named[real[-1]]
        seen.update(named)
    for (c, t), l in zip(rs, lists):
        if c:
            print(
                '   REPLAY FAILED (exit %d) for: %s: %s'
                % (c, ' '.join(l)[:200], t.strip().split('\n')[-1][:200])
            )
    rs += first  # the other call's status and output count like a list's
    replay_panics = panics(
        'the kernel replay', [c for c, _ in rs], '\n'.join(t for _, t in rs), 'replay.*.log'
    )
    # The audit writes its result (the lines on the named theorems, and the listing) to this file.
    # Setting the variable also replaces a value that the caller happens to have set.
    env2 = dict(os.environ, AUDIT_OUT='../statement-listing.txt')  # Lean starts in ROOT
    env2.pop('AUDIT_PART', None)
    rc2, o2 = (
        (-1, '')
        if short_of('the audit, with %d parts in parallel,' % SIDE, AUDIT_GIB)
        else sh_(['lake', 'env', 'lean', '../Audit.lean'], ROOT, 'audit.log', env2, AUDIT_CAP)
    )
    for l in o2.split('\n'):
        if re.search(r':\d+:\d+: error', l):
            print('   ' + l.replace('../', OUT + '/')[:300])  # a person gets the whole path
    audit_panics = panics('the audit', [rc2], o2, 'audit.log')
    A = [
        l[len('AUDIT ' + nonce + ' ') :]
        for l in o2.split('\n')
        if l.startswith('AUDIT ' + nonce + ' ')
    ]
    A, fault = take_result(A, 'statement-listing.txt', nonce)
    if fault:
        print('   THE AUDIT\'S RESULT IS REJECTED: ' + fault)
        rc2 = rc2 or 1  # the audit then counts as failed, whatever it printed
    return seen, skip, all(c == 0 for c, _ in rs), rc2, A, replay_panics, audit_panics, wide


def take_result(A, p, nonce):
    """Takes the audit's result file p only if it has the sha256 that the audit printed in its lines
    A; a file that is not taken is removed. Returns what with_result returns."""
    said = [
        m.group(1)
        for m in (re.search(r'^result: .*sha256 of the whole file (\w{64})$', l) for l in A)
        if m
    ]
    ok = not os.path.islink(p) and os.path.isfile(p) and [lclib.sha(open(p, 'rb').read())] == said
    if not ok and os.path.lexists(p):
        remove(os.path.basename(p), OUT_FD)  # no rejected file is left under the listing's name
    return with_result(A, p if ok else None, nonce)


def split_result(p, nonce):
    """Parses the audit's result file p: the line "AUDIT-RESULT 1 NONCE K", K lines on
    the named theorems, the line AUDIT-LISTING, then the listing. The K lines are taken
    by count, so that nothing inside a line can end them early.
    Returns (the K lines, the listing's text), or a sentence that says what is wrong."""
    try:
        t = open(p, 'rb').read().decode('utf-8')
    except (OSError, UnicodeDecodeError):
        return 'the result file cannot be read as text'
    h, _, rest = t.partition('\n')
    m = re.fullmatch(r'AUDIT-RESULT 1 ([0-9a-f]+) (\d+)', h)
    if not m:
        return 'the result file does not start with the first line of a result ' 'file'
    if m.group(1) != nonce:
        return 'the result file carries the random tag of a different run'
    k = int(m.group(2))
    ls = rest.split('\n', k + 1)
    if len(ls) != k + 2 or ls[k] != 'AUDIT-LISTING':
        return (
            'the result file does not contain the %d lines that its first '
            'line announces, followed by the separator line'
        ) % k
    return ls[:k], ls[k + 1]


def with_result(A, p, nonce):
    """Replaces the line of A (the audit's printed lines) that announces the result file by the
    lines on the named theorems, read from that file, p, and cuts the file down to the listing. p is
    None if the file is missing or does not have the sha256 that the audit printed.
    Returns (the lines, an error message or None)."""
    mk = [
        (i, m)
        for i, m in (
            (
                i,
                re.fullmatch(
                    (
                        r'named theorems: their lines, (\d+) in number, stand in the '
                        r'result file and are not printed'
                    ),
                    l,
                ),
            )
            for i, l in enumerate(A)
        )
        if m
    ]
    if not mk and not p:
        return A, None
    if not p:
        return (
            A,
            (
                'the audit says that the lines on the named theorems are in its '
                'result file, but that file is missing or is not the one that '
                'this run\'s audit wrote (%s/audit.log)'
            )
            % OUT,
        )
    r = (
        (
            'the audit wrote a result file but did not print how many lines '
            'it contains (%s/audit.log)'
        )
        % OUT
        if not mk
        else (
            'the audit announces its result file %d times' % len(mk)
            if len(mk) != 1
            else split_result(p, nonce)
        )
    )
    if not isinstance(r, str) and len(r[0]) != int(mk[0][1].group(1)):
        r = 'the result file contains %d lines, but the audit announced %s' % (
            len(r[0]),
            mk[0][1].group(1),
        )
    if isinstance(r, str):
        remove(os.path.basename(p), OUT_FD)  # no rejected file is left under the listing's name
        return A, r
    mk = [mk[0][0]]
    open(fresh(os.path.basename(p)), 'w', encoding='utf-8', newline='').write(r[1])
    return A[: mk[0]] + r[0] + A[mk[0] + 1 :], None


def read_headline(l, okname):
    """Parses a "headline" line of top-theorems.txt (the top of that file describes its forms):
        NAME headline BINDER | BINDER .. => HEAD | walk C #j .. | report C #j .. | .. met WITNESS ..
    Returns (name, binders, head, arguments, witnesses), or a sentence that says which part could
    not be read. A binder is (constant, positions of earlier binders); an argument is (True for walk
    and False for report, constant, positions of binders); a witness is a number or a name.
    """
    p = l.split()
    parts = lambda ws: [x.split() for x in ' '.join(ws).split(' | ')]
    if (
        p.count('=>') != 1
        or p.count('met') != 1
        or not 2 < p.index('=>') < p.index('met') - 1 < len(p) - 2
    ):
        return (
            'after the word headline come the binders, then "=>" once, the '
            'conclusion, then the word "met" once, and the witnesses; none '
            'of the three parts may be empty'
        )
    bs, cc, ws = (
        parts(p[2 : p.index('=>')]),
        parts(p[p.index('=>') + 1 : p.index('met')]),
        parts(p[p.index('met') + 1 :]),
    )

    def term(x, below, what):
        if not x or not okname.fullmatch(x[0]):
            return '%s: "%s" does not begin with a full name' % (what, ' '.join(x))
        if not all(re.fullmatch(r'#(0|[1-9][0-9]{0,2})', j) and int(j[1:]) < below for j in x[1:]):
            return (
                '%s: after %s only binders may follow, given by position ("#0" '
                'is the first), and only binders that %s'
            ) % (what, x[0], 'come before this one' if what.startswith('binder') else 'exist')
        return (x[0], [int(j[1:]) for j in x[1:]])

    B = [term(x, i, 'binder %d' % (i + 1)) for i, x in enumerate(bs)]
    # The parts are checked in the order in which they appear, so that the first error is the one
    # that is reported.
    for x in B:
        if isinstance(x, str):
            return x
    if len(cc[0]) != 1 or not okname.fullmatch(cc[0][0]):
        return (
            'the conclusion: after "=>" comes the full name of the predicate '
            'by itself, then " | " and the first argument'
        )
    if len(cc) < 2:
        return 'the conclusion: no argument is named'
    Z = [
        (
            term(x[1:], len(bs), 'argument %d' % (i + 1))
            if x[:1] in (['walk'], ['report'])
            else 'argument %d: "%s" does not begin with the word walk or report'
            % (i + 1, ' '.join(x))
        )
        for i, x in enumerate(cc[1:])
    ]
    for x in Z:
        if isinstance(x, str):
            return x
    if not any(x[0] == 'walk' for x in cc[1:]):
        return (
            'the conclusion: no argument is marked "walk", so nothing would ' 'be walked for choice'
        )
    if len(ws) != len(bs):
        return 'the witnesses: %d are named for %d binders' % (len(ws), len(bs))
    for i, x in enumerate(ws):
        if len(x) != 1 or not (re.fullmatch(r'0|[1-9][0-9]{0,17}', x[0]) or okname.fullmatch(x[0])):
            return (
                'witness %d: "%s" is neither a number (of at most 18 digits, '
                'without a leading zero) nor a full name'
            ) % (i + 1, ' '.join(x))
    return (
        p[0],
        B,
        cc[0][0],
        [(x[0] == 'walk',) + z for x, z in zip(cc[1:], Z)],
        [int(x[0]) if x[0].isdigit() else x[0] for x in ws],
    )


def verdicts_complete(A, tops, heads):
    """Returns what is missing from the audit's lines A: every theorem that top-theorems.txt lists
    (tops, heads) must have its verdict line. A closed theorem: "NAME: binders PASSED", with
    "choice PASSED below C" for each of its constants. A general theorem: "NAME: general". A
    headline: a line that starts with its five verdicts as bare words (a name from the library,
    printed later in the line, could contain such words) and has "choice PASSED below C" for each
    constant marked walk; and one report line for each constant marked report, each binder's
    constant except Nat, each witness that is a name, and the implicit arguments."""
    miss = []
    for n, bs, hd, args, ws in heads:
        l = [x for x in A if x.startswith(n + ': ')]
        if len(l) != 1:
            miss.append('%s: %d lines' % (n, len(l)))
            continue
        nw = len({c for k, c, _ in args if k})
        if not l[0].startswith(
            (
                '%s: headline; binders PASSED, head PASSED, arguments PASSED, '
                'hypotheses PASSED, choice PASSED below all that are marked walk '
                '(%d); binders PASSED ('
            )
            % (n, nw)
        ):
            miss.append(n + ': its line does not begin with the five verdicts, all PASSED')
        for w in ['head PASSED: %s' % hd] + ['choice PASSED below %s' % c for k, c, _ in args if k]:
            if '; %s (' % w not in l[0]:
                miss.append('%s: no "%s"' % (n, w))
        for c in sorted(
            {c for k, c, _ in args if not k}
            | {c for c, _ in bs if c != 'Nat'}
            | {w for w in ws if isinstance(w, str)}
        ) + ['the implicit arguments']:
            if sum(1 for x in A if x.startswith('%s, below %s, no verdict: ' % (n, c))) != 1:
                miss.append('%s: not exactly one report below %s' % (n, c))
    for n, k, ss in tops:
        l = [x for x in A if x.startswith(n + ': ')]
        if len(l) != 1:
            miss.append('%s: %d lines' % (n, len(l)))
            continue
        if k is None:
            if not l[0].startswith(n + ': general;'):
                miss.append(n + ': not reported as general')
            continue
        if not l[0].startswith(n + ': binders PASSED;'):
            miss.append(n + ': no "binders PASSED"')
        for c in ss:
            if ('choice PASSED below %s (' % c) not in l[0]:
                miss.append('%s: no "choice PASSED below %s"' % (n, c))
    return miss


def tally_counts(A, tops, heads, allow):
    """Fills counts with what the end of the output reports about the audit. Numbers counted from
    the data files (tops, heads, allow) say nothing about what the audit checked; the others are
    read from the audit's lines A. Parts of the audit for which nothing is listed go into notrun."""
    (
        counts['closed top theorems'],
        counts['general theorems'],
        counts['schemes named'],
        counts['allowed steps'],
    ) = (
        sum(1 for _, k, _ in tops if k is not None),
        sum(1 for _, k, _ in tops if k is None),
        len({x for _, _, ss in tops for x in ss}),
        len(allow),
    )
    counts['headlines with named binders'] = len(heads)
    if heads:
        counts['constants walked for choice below the headlines'] = len(
            {c for h in heads for k, c, _ in h[3] if k}
        )
    nh = [
        re.fullmatch(
            (
                r'listing: headlines WITHOUT their lists and declarations in the '
                r'listing \(listing-for.txt names others\): (\d+) of (\d+)'
            ),
            l,
        )
        for l in A
    ]
    nh = [m for m in nh if m]
    if nh:
        counts['headlines WITHOUT their declarations in the listing'] = int(nh[0].group(1))
        counts['of headlines'] = int(nh[0].group(2))
    pg = [
        re.fullmatch(
            (
                r'syntax, no verdict: in all \d+ modules of ours, (\d+) '
                r'declarations program Lean'
            ),
            l,
        )
        for l in A
    ]
    pg = [m for m in pg if m]
    if pg:
        counts['declarations that program Lean (macros, notations, elaborators)'] = int(
            pg[0].group(1)
        )
    cp = [
        re.match(
            (
                r'axioms PASSED: every declaration that Lean attributes to a module '
                r'of the library was checked: all \d+ declarations in all \d+ '
                r'modules, and all (\d+) copies'
            ),
            l,
        )
        for l in A
    ]
    cp = [m for m in cp if m]
    if cp:
        counts[('copies of theorems that are in more than one module, each ' 'checked')] = int(
            cp[0].group(1)
        )
    nb = [
        re.match(
            (
                r'listing: closed theorems WITHOUT their lists and declarations '
                r'in the listing \(listing-for.txt names others\): (\d+) of (\d+)'
            ),
            l,
        )
        for l in A
    ]
    nb = [m for m in nb if m]
    if nb:
        counts['closed theorems WITHOUT their declarations in the listing'] = int(nb[0].group(1))
        counts['of closed theorems'] = int(nb[0].group(2))
    cl = [
        re.match(
            (r'clashes, no verdict: (\d+) names are declared in more than one ' r'module of ours'),
            l,
        )
        for l in A
    ]
    cl = [m for m in cl if m]
    if cl:
        counts[
            (
                'names declared in more than one module that are not copies of '
                'one theorem (if not 0, no file can import the whole library)'
            )
        ] = int(cl[0].group(1))
    pb = [
        re.match(
            (
                r'syntax, no verdict: the most declarations that program Lean in '
                r'the modules below ONE named statement: (\d+)'
            ),
            l,
        )
        for l in A
    ]
    pb = [int(m.group(1)) for m in pb if m]
    if pb:
        counts[
            ('declarations that program Lean in the modules below one named ' 'theorem, AT LEAST')
        ] = max(pb)
    if not tops and not heads:
        notrun.append('audit of top theorems (none named)')
    if any(not ss and k is not None for _, k, ss in tops):
        notrun.append('audit of choice (a closed top theorem without a scheme)')
    if not (heads or any(k is not None for _, k, _ in tops)):
        counts[
            'verdicts on binders or on Classical.choice (top-theorems.txt has no closed line and '
            'no headline)'
        ] = 0


def verdict(step, ok, t):
    """Prints one verdict, "PASSED: " or "FAILED: " and t. If ok is false, step joins the list of
    failed steps, which the run's last line names."""
    print('   %s: %s' % ('PASSED' if ok else 'FAILED', t), flush=True)
    if not ok and step not in failed:
        failed.append(step)


def graph():
    """Returns (for each module what it imports; a message for each file whose header cannot be
    read: such a module is entered with no imports)."""
    g, unread = {}, []
    for rel in FILES:
        if lclib.REL.fullmatch(rel):
            try:
                g[lclib.mod_of(rel)] = lclib.imports_of(text(rel))
            except (ValueError, UnicodeDecodeError) as e:
                g[lclib.mod_of(rel)] = []
                unread.append('%s: its header cannot be read: %s' % (rel, e))
    return g, unread


def under(m, p):
    """True if the module m is p or lies below p by its name: under A.B are A.B and A.B.C, not
    A.BC."""
    return m == p or m.startswith(p + '.')


def long_lines():
    """A verdict of the step "tree": no line of a Lean file has more than 100 characters, except in
    the files that scripts/long-lines.txt lists. A row: the path, how many such lines the file may
    have, the longest that it may have, separated by tabs. By count, not by line number or text, so
    that a change elsewhere in the file does not break the row."""
    allow, bad, loose = {}, [], 0
    if not os.path.isfile(ROOT + '/scripts/long-lines.txt'):
        print('   scripts/long-lines.txt is absent: no file may have a long line')
    for l in data('long-lines.txt'):
        p = l.split('\t')
        if len(p) != 3 or not all(re.fullmatch('[0-9]{1,9}', x) for x in p[1:]):
            bad.append(
                'long-lines.txt: a row that is not "path, count, length" with tabs: ' + l[:80]
            )
        elif p[0] in allow:
            bad.append('long-lines.txt: a second row for ' + p[0])
        else:
            allow[p[0]] = (int(p[1]), int(p[2]))
    bad += [
        'long-lines.txt: %s is not a file of this library' % f
        for f in allow
        if f not in FILES and f not in ASK
    ]
    files = lines = 0
    for rel in FILES + ASK:
        over = [len(l) for l in text(rel).split('\n') if len(l) > 100]
        most, longest = allow.get(rel, (0, 100))
        files, lines = files + bool(over), lines + len(over)
        if len(over) > most or max(over, default=0) > longest:
            bad.append(
                '%s has %d lines of more than 100 characters, the longest of %d; %s'
                % (
                    rel,
                    len(over),
                    max(over),
                    (
                        'long-lines.txt allows it %d, of at most %d' % (most, longest)
                        if rel in allow
                        else 'long-lines.txt has no row for it'
                    ),
                )
            )
        loose += len(over) < most
    for b in bad[:30]:
        print('   ' + b)
    if len(bad) > 30:
        print('   ... and %d more' % (len(bad) - 30))
    verdict(
        'tree',
        not bad,
        (
            'lines of more than 100 characters: %d, in %d files, all within the rows of '
            'long-lines.txt; %d rows allow more than their file has; %d problems'
            % (lines, files, loose, len(bad))
            if not bad
            else 'lines of more than 100 characters: %d, in %d files; %d problems'
            % (lines, files, len(bad))
        ),
    )


ASK_HEAD = ['Reads:', 'Command:', 'Takes:', 'Its print means:', 'It does not mean:']


def asking_files(mods):
    """A verdict of the step "tree", printed only if there are asking files (ASK). Each one: its
    header can be read; no "module" or "prelude"; it imports files of the library (mods) and of the
    packages only, and no asking file, because none is compiled; above its first import stand the
    five labels of ASK_HEAD, in that order; it declares no theorem whose name, or whose name behind
    a namespace, is on top-theorems.txt or claimed-theorems.tsv. scripts/RULES.txt, "Asking
    files"."""
    bad = []
    named = {l.split()[0] for l in data('top-theorems.txt')}
    named |= {l.split('\t')[0] for l in data('claimed-theorems.tsv')}
    for rel in ASK:
        try:
            t = text(rel)
            imps = lclib.imports_of(t)
        except (ValueError, UnicodeDecodeError) as e:
            bad.append('%s: its header cannot be read: %s' % (rel, e))
            continue
        code = code_of(t)
        if re.match(r'\s*(module|prelude)\b', code):
            bad.append('%s begins with "module" or "prelude"' % rel)
        for j in imps:
            if j.split('.')[0] in lclib.PACKAGE_ROOTS:
                continue
            if under(j, 'Ask'):
                bad.append(
                    '%s imports %s: an asking file is not compiled, so nothing can import it'
                    % (rel, j)
                )
            elif j not in mods:
                bad.append('%s imports %s, which is not a file of this library' % (rel, j))
        m = re.search(r'(?m)^import\b', code)
        head, at = t[: m.start()] if m else t, 0
        for w in ASK_HEAD:
            k = head.find(w, at)
            if k < 0:
                bad.append(
                    '%s: above its first import the label "%s" is missing, or stands before an '
                    'earlier one of: %s' % (rel, w, ' | '.join(ASK_HEAD))
                )
                break
            at = k + len(w)
        for n in re.findall(
            r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|@\[[^\]\n]*\])[ \t]+)*'
            r'(?:theorem|lemma)[ \t]+([^\s:({\[]+)',
            code,
        ):
            hit = sorted(x for x in named if x == n or x.endswith('.' + n))
            if hit:
                bad.append(
                    '%s declares the theorem %s, and the lists name %s: what an asking file '
                    'declares is not built, replayed or audited' % (rel, n, hit[0])
                )
    for b in bad[:30]:
        print('   ' + b)
    verdict(
        'tree',
        not bad,
        'asking files (below Ask/; not built, not replayed, not audited): %d; %d problems'
        % (len(ASK), len(bad)),
    )


def step_tree():
    """The step "tree". Its own verdict fails for every fault that was entered in odd_things while
    the Lake files were read and the copy was made, for every entry of ODD_BYTES (a character
    outside the table, "#lang", invalid UTF-8), for a file under a package's name, a header that
    cannot be read or begins with "module" or "prelude", an import of a module, other than a
    package's, that is no file of this library, and if there is no Lean file at all. Then come the
    verdicts of asking_files, if there are asking files, and of long_lines."""
    print(
        (
            '== tree: every file is a regular file; no '
            'two names in a directory differ only in letter case; every '
            'import of a module of this library names one of these files; no '
            '"module" or "prelude" header; long lines only where a list allows them'
        ),
        flush=True,
    )
    bad = list(odd_things) + ODD_BYTES
    mods = {lclib.mod_of(r) for r in FILES if lclib.REL.fullmatch(r)}
    bad += [
        'under a package\'s name: ' + r
        for r in FILES
        if r.split('/')[0].removesuffix('.lean') in lclib.PACKAGE_ROOTS
    ]
    for rel in FILES:
        try:
            t = text(rel)
            imps = lclib.imports_of(t)
        except (ValueError, UnicodeDecodeError) as e:
            bad.append('%s: its header cannot be read: %s' % (rel, e))
            continue
        if re.match(r'\s*(module|prelude)\b', code_of(t)):
            bad.append(
                (
                    '%s begins with "module" or "prelude": this library does not use '
                    'them, and it is not known what the replay does with the private '
                    'part of such a file'
                )
                % rel
            )
        for j in imps:
            if j.split('.')[0] in lclib.PACKAGE_ROOTS:
                continue
            if j not in mods:
                bad.append(
                    '%s imports %s, which is not a file of this library%s%s'
                    % (
                        rel,
                        j,
                        ' (a file named *_wip.lean)' if j.endswith('_wip') else '',
                        ' (an asking file: no file of the library may import one)'
                        if under(j, 'Ask')
                        else '',
                    )
                )
    for b in bad[:30]:
        print('   ' + b)
    for x in lake_other.values() if a.other_lake else ():
        print('   NOT REJECTED, because --other-lake was given: ' + x)
    if not lake_other and not lake_code:
        print(
            (
                '   the Lake files (%s) have the sha256 that this check.py '
                'expects; no lakefile.lean'
            )
            % ', '.join(LAKE_FILES)
        )
    if lake_folder:
        print(
            '   not examined: .lake in the top directory (Lake\'s own '
            'directory: packages, compiled files). Nothing in it is checked; '
            'the build uses a copy of its packages as they are'
        )
    verdict('tree', not bad and bool(FILES), '%d Lean files; %d problems' % (len(FILES), len(bad)))
    verdict('tree', *wide_pinned(sorted(lclib.mod_of(r) for r in FILES)))
    if ASK:
        asking_files(mods)
    long_lines()


def code_of(t, strings=False):
    """Returns t with comments and the contents of string and character literals blanked (line
    breaks kept). With strings=True these literals are kept, and only comments are blanked.
    It approximates Lean's lexer and can be fooled: scripts/RULES.txt, "How comments are blanked".
    """
    out, i, n, e = [], 0, len(t), 0
    blank = lambda s: ''.join(ch if ch == '\n' else ' ' for ch in s)
    while i < n:
        c = t[i]
        # e: where the last comment ended (0 at the start)
        if t.startswith('--', i) and (i == e or t[i - 1] in ' \t\r\n'):
            j = t.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = e = j
        elif (
            t.startswith('/-', i)
            and (i == e or t[i - 1] in ' \t\r\n')
            and not re.compile(r'/-[-!](?:[^ \n]|[ \n]*(?:--|/-))').match(t, i)
        ):
            d, j = 1, min(i + 3, n)
            while j < n and d:
                if t.startswith('-/', j):
                    d -= 1
                    j += 2
                elif t.startswith('/-', j):
                    d += 1
                    j += 2
                else:
                    j += 1
            out.append(blank(t[i:j]))
            i = e = j
        elif c == '\u00ab':
            j = t.find('\u00bb', i)
            j = n if j < 0 else j + 1
            out.append(t[i:j])
            i = j
        elif (
            c == 'r'
            and re.match(r'r#*"', t[i : i + 40])
            and not (i and (t[i - 1].isalnum() or t[i - 1] in "_'.!?"))
        ):
            h = re.match(r'r(#*)"', t[i : i + 40]).group(1)
            j = t.find('"' + h, i + 2 + len(h))
            j = n if j < 0 else j + 1 + len(h)
            out.append(t[i:j] if strings else blank(t[i:j]))
            i = j
        elif c == '"':
            interp = i > 0 and t[i - 1] == '!'
            j, buf, depth = i + 1, ['"'], 0
            while j < n and (t[j] != '"' or depth):
                if t[j] == '\\' and not depth:
                    buf.append(' \n' if t[j + 1 : j + 2] == '\n' else '  ')
                    j += 2
                    # a backslash at the end of a line (a string gap): the line break is kept, like
                    # every other
                    continue
                if interp and t[j] == '{':
                    depth += 1
                elif interp and t[j] == '}' and depth:
                    depth -= 1
                buf.append(t[j] if (depth or t[j] in '\n}') else ' ')
                j += 1
            out.append(t[i : j + 1] if strings else ''.join(buf) + '"')
            i = min(j + 1, n)
        elif (
            c == "'"
            and re.match(r"'(\\.[^']{0,6}|[^'\\\n])'", t[i : i + 10])
            and not (i and (t[i - 1].isalnum() or t[i - 1] in "_'"))
        ):
            m = re.match(r"'(\\.[^']{0,6}|[^'\\\n])'", t[i : i + 10])
            out.append(m.group(0) if strings else blank(m.group(0)))
            i += m.end()  # a line break inside it is kept, like every other
        else:
            out.append(c)
            i += 1
    return ''.join(out)


# Each pattern of the word list is searched in the text with comments blanked (code_of) and, except
# three words, in the raw text too. scan-exceptions.txt lists the legitimate lines that the
# raw search hits; its sha256 is pinned here. scripts/RULES.txt, "Every word is searched twice".
# PINS: BEGIN
LIST_SUM = '7041d2d29034acc502ed0e3c175f03f120c12f685baba207754bf8a325e0af15'
# PINS: END
pin_shape('LIST_SUM', LIST_SUM)
# Appended to a reported match that only the raw search hits: a comment or a string according to
# code_of.
RAW_ONLY = ' [raw text only]'
ex, excode, used, granted, noreason = {}, set(), {}, {}, []


def listed(rel, n, line, code):
    """Does scan-exceptions.txt cover line n of rel? code: the match also occurs in code_of's text.
    One entry covers one line, for all rules."""
    if (rel, n) not in granted:
        granted[(rel, n)] = used.get((rel, line), 0) < ex.get((rel, line), 0)
        if granted[(rel, n)]:
            used[(rel, line)] = used.get((rel, line), 0) + 1
    return granted[(rel, n)] and (not code or (rel, line) in excode)


def two_looks(rel, t, rx, strings, raw_rx=None):
    """Returns the matches of rx in the text t of rel that scan-exceptions.txt does not cover:
    [(line, the matched text, '' or RAW_ONLY)]. First the search in code_of's text, then the raw
    search (with raw_rx, if it is given)."""
    bare = lambda s: s.replace('\u00ab', ' ').replace('\u00bb', ' ')
    lines, met, wide = t.split('\n'), {}, set()
    for code, s, r in ((True, bare(code_of(t, strings)), rx), (False, bare(t), raw_rx or rx)):
        for x in r.finditer(s):
            p = (s.count('\n', 0, x.start()) + 1, ' '.join(x.group(0).split()))
            met.setdefault(p, code)
            if '\n' in x.group(0):
                # A match that spans a line break is never covered: an entry records only the first
                # line, and the match consumes every word on the later ones.
                wide.add(p)
    # no entry covers a comment delimiter that is left in code: after it code_of is out of step with
    # Lean, and a word could hide there
    return [
        (n, w, '' if code else RAW_ONLY)
        for (n, w), code in sorted(met.items())
        if w in ('--', '/-') or (n, w) in wide or not listed(rel, n, lines[n - 1], code)
    ]


WORDS = ['sorry', 'axiom', 'opaque', 'unsafe', 'native_decide', 'implemented_by', 'extern']
MORE = [
    'sorryAx',
    'ofReduceBool',
    'ofReduceNat',
    'trustCompiler',
    'unsafeCast',
    'csimp',
    'unsafeBaseIO',
    'unsafeIO',
    'lcProof',
    'lcAny',
    'skipKernelTC',  # up to here: other names for the same things; none is an ordinary word
    # Lean's record of which constants its structural-recursion elaborator generated. A guard reads
    # it (OnBytes/Guard/Cmd.lean), and a meta-program could add an entry. scan-exceptions.txt allows
    # the guard's own line as code.
    'eqnInfoExt',
    # The function that tags the auxiliary constants ._sparseCasesOn_N. It is not private, so a
    # meta-program in a file of the library could call it. Nothing in this script reads the tag; the
    # word stays rejected because no file of the library needs it.
    'markSparseCasesOn',
    # The code generator compiles f from f._unsafe_rec if that constant exists: scripts/RULES.txt,
    # "The name part _unsafe_rec".
    '_unsafe_rec',
    # The next four: each makes an opaque constant, which otherwise only the audit would see.
    'partial',
    'register_option',
    'initialize',
    'builtin_initialize',
    # Lean stops reading a file at this command and reports no error: what stands below it (a
    # theorem, a "#guard" command) would be in the text and not in the compiled file.
    '#exit',
]
# "+ native" is matched too: guillemets become spaces before both searches, and "+«native»" would
# also be the option (Lean's parser accepts such guillemets: tested with a harmless option).
AHEAD = r")(?![A-Za-z0-9_'!?])|\+[ ]?native|native\s*:=\s*true"
# for code_of's text. The last two alternatives: a "--" or "/-" that code_of has left in its output
# is at a place where it starts no comment (scripts/RULES.txt, "How comments are blanked").
# Legitimate code that this rejects:
# "{x : Int //-1 < x}" and "foo-- a comment", written without a space
OLD_RX = re.compile("(" + '|'.join(WORDS + MORE) + AHEAD + "|--|/-")
# for the raw text. The last alternative: a string that starts with "/--" or "/-!"; as a notation's
# token it would be a token for Lean where code_of reads a comment
OLD_RAW_RX = re.compile(
    "("
    + '|'.join(w for w in WORDS + MORE if w not in ('partial', 'axiom', 'sorry'))
    + AHEAD
    + '|"[ ]*/-[-!]'
)
# The word list does not cover what programs Lean during compilation (macros, notations,
# elaborators): the audit counts that in the compiled files, where no lexing trick hides it. A rule
# on such words would hinder ordinary use and catch nothing that the audit does not catch.


# Three text rules on verify-on-bytes, the Lean text below OnBytes.Main: a hand translation of
# cp_verify into Lean, from which this repository builds no program. Each only rejects more. They
# are explained in scripts/RULES.txt; what "the program" means in their names: there, "The three
# rules on the program".
ONE = 'OnBytes.Main'
ROOTS = [ONE]  # the first two rules are applied to each root separately, with separate verdicts
# THE PROGRAM'S SOURCE: in the modules that the root imports, directly or indirectly, no command
# programs Lean. Rejected: (a) every word in PROGRAMS; (b) to (f) below. scripts/RULES.txt, "The
# program's source".
PROGRAMS = [
    'run_cmd',
    'run_elab',
    'run_meta',
    'run_tac',
    'run_conv',
    'run_tacq',
    'run_io',
    'by_elab',
    'by_elabq',  # run_cmd to by_elabq: run at once, as a command, inside a proof or inside a term
    'macro',
    'macro_rules',
    'syntax',
    'elab',
    'elab_rules',
    'elab_stx_quot',
    'binder_predicate',
    'notation3',  # macro to notation3: define new syntax and its meaning
    'simproc',
    'simproc_decl',
    'simproc_pattern%',
    'dsimproc',
    'dsimproc_decl',
    'grind_propagator',
    'set_library_suggestions',
    'add_aesop_rules',
    'erase_aesop_rules',  # simproc to here: register procedures that a tactic will call
    'solve_by_elim',
    'apply_rules',
    'apply_assumption',
    # solve_by_elim, apply_rules and apply_assumption (above) and plausible (below): tactics that
    # take a program from the caller, in a field of their configuration or as an instance that is
    # run. aesop, which takes one as a rule, falls under (b)
    'plausible',
    'compile_def%',
    'compile_inductive%',
    'suppress_compilation',
    'unsuppress_compilation',  # these four: Mathlib's commands on what is compiled, and from what
    'docs_to_verso',
]  # docs_to_verso: doc comments are read as documents; Lean elaborates their code as commands
# (b) to (f): scripts/RULES.txt, "The program's source, (b) to (f)".
PROGRAM_RX = re.compile(
    '|'.join(re.escape(w) for w in PROGRAMS if w[-1] == '%')
    + r"|(?:"
    + '|'.join(re.escape(w) for w in PROGRAMS if w[-1] != '%')
    + (
        r"|(?:register_|declare_|builtin_|"
        r"aesop)[A-Za-z0-9_'!?%]*)(?![A-Za-z0-9_'!?])|#(?!(?:print|"
        r"guard)(?![A-Za-z0-9_'!?]))[A-Za-z_][A-Za-z0-9_'!?]+|(?:@\[|"
        r"attribute\s*\[)(?:[^\[\]\"]|\[[^\[\]]*\]|\"(?:[^\"\\]|"
        r"\\.)*\")*?(?<![A-Za-z0-9_'.!?])init(?![A-Za-z0-9_'!?])|(?m:^[ "
        r"\t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:scoped(?:\[[^\]\n]*\])?|local|"
        r"private|protected)[ \t]+)*(?:notation|infixl|infixr|infix|prefix|"
        r"postfix)(?![A-Za-z0-9_'!?])[^\n]*?\"[^\"\n]*[A-Za-z0-9_\x60#\[][^\"\n]*\")|"
        r"_unsafe_rec(?![A-Za-z0-9_'!?])"
    )
)
# What that rule does not catch, and THE PROGRAM'S OUTCOME (the outcome of a run is decided in one
# place; ENDS): scripts/RULES.txt. Each entry of ENDS: its name in the printed line; the pattern;
# the modules that are searched (None: all); per file, the only definitions in which a match is
# allowed.
ENDS = [
    (
        'a word of the verdict, Process.exit',
        r"VERDICT|(?<![A-Za-z])YES(?![A-Za-z])|WITHIN LIMITS|PASSED|Process\s*\.\s*exit",
        None,
        {
            'OnBytes/Model/Stages.lean': {'CallEnd.lastLine'},
            'OnBytes/Shell/Lines.lean': {'Line.text'},
            'OnBytes/Shell/Call.lean': {'usage'},
        },
    ),
    (
        'what makes a passing ending',
        (
            r"\.\s*(?:yes|withinLimits|partPassed|testPassed)(?![A-Za-z0-9_'!?])|"
            r"(?<![A-Za-z0-9_'!?])(?:\.\s*)?ofNat(?![A-Za-z0-9_'!?])|"
            r"(?<![A-Za-z0-9_'!?])(?:Ending|CallEnd)\s*\."
        ),
        r"(?<![A-Za-z0-9_'!?])(?:Ending|CallEnd)(?![A-Za-z0-9_'!?])",
        {
            'OnBytes/Model/Stages.lean': {'CallEnd.lastLine', 'CallEnd.status', 'cpStagesRun'},
            'OnBytes/Shell/Ask.lean': {'Ending.status', 'finishWork'},
            'OnBytes/Shell/Lines.lean': {'Line.text', 'before', 'verdict'},
            'OnBytes/Shell/Whole.lean': {'earlyEnd', 'partEnd'},
            'OnBytes/Shell/Ops.lean': {'mainIO'},
        },
    ),
    (
        'what turns an ending into a number',
        r"\.\s*(?:status|ctorIdx|toCtorIdx|casesOn)(?![A-Za-z0-9_'!?])",
        r"(?<![A-Za-z0-9_'!?])(?:Ending|CallEnd)(?![A-Za-z0-9_'!?])",
        {
            'OnBytes/Model/Stages.lean': {'CallEnd.status'},
            'OnBytes/Shell/Ask.lean': {'Ending.status'},
            'OnBytes/Shell/Ops.lean': {'mainIO'},
        },
    ),
    (
        'a status 0 or 3',
        (
            r"(?<![A-Za-z_])(?:return|pure)[\s(]*(?:(?:<\||\$)[\s(]*)?0*[03](?![A-Za-z0-9_.])|"
            r"=>[\s(]*0*[03](?![A-Za-z0-9_.])|\(\s*0*[03]\s*:\s*UInt32\s*\)|"
            r"(?<![A-Za-z0-9_'!?])(?:then|else)[\s(]*0*[03](?![A-Za-z0-9_.])"
        ),
        r"(?<![A-Za-z0-9_'!?])(?:(?:IO|BaseIO)\s+UInt32|Ending|CallEnd)(?![A-Za-z0-9_'!?])",
        {
            'OnBytes/Model/Stages.lean': {'CallEnd.status'},
            'OnBytes/Shell/Ask.lean': {'Ending.status'},
            'OnBytes/Shell/Ops.lean': {'codeOf'},
            'OnBytes/Shell/Lines.lean': {'Unread.ofCode'},
        },
    ),
    (
        'the functions that print the exit code in the line for programs',
        r"(?<![A-Za-z0-9_'!?])closing(?:Whole|Part)(?![A-Za-z0-9_'!?])",
        None,
        {
            'OnBytes/Shell/Lines.lean': {'closingWhole', 'closingPart', 'before'},
        },
    ),
    (
        'where a pass is born before the ending',
        (
            r"\.\s*(?:passed|accepted)(?![A-Za-z0-9_'!?])|(?<![A-Za-z0-9_'!?])(?:StageEnd|"
            r"Verdict)\s*\."
        ),
        None,
        {
            'OnBytes/Model/Stages.lean': {'lastLine', 'stageFault', 'passedWithWork'},
            'OnBytes/Proof/File.lean': {'check'},
            'OnBytes/ChecksWithHashAsArgument/M/Proof/File.lean': {'check'},
            'OnBytes/Toy/Product.lean': {'product'},
            'OnBytes/Toy/Links.lean': {'links'},
            'OnBytes/Shell/Toys.lean': {'verdictOf'},
            'OnBytes/Model/VerifyStages.lean': {'requestStage'},
            'OnBytes/ChecksWithHashAsArgument/M/Model/VerifyStages.lean': {'requestStage'},
            'OnBytes/Shell/Ask.lean': {'finishTest'},
        },
    ),
    (
        'a status of three digits or more, with "_", or in another base',
        (
            r"(?<![A-Za-z_])(?:return|pure)[\s(]*(?:(?:<\||\$)[\s(]*)?(?:0*[1-9][0-9]{2,}|"
            r"[0-9]+_[0-9_]*|0[xXbBoO][0-9A-Fa-f_]+)(?![A-Za-z0-9_.])|=>[\s(]*(?:0*[1-9][0-9]{2,}|"
            r"[0-9]+_[0-9_]*|0[xXbBoO][0-9A-Fa-f_]+)(?![A-Za-z0-9_.])|\(\s*(?:0*[1-9][0-9]{2,}|"
            r"[0-9]+_[0-9_]*|0[xXbBoO][0-9A-Fa-f_]+)\s*:\s*UInt32\s*\)|"
            r"(?<![A-Za-z0-9_'!?])(?:then|else)[\s(]*(?:0*[1-9][0-9]{2,}|[0-9]+_[0-9_]*|"
            r"0[xXbBoO][0-9A-Fa-f_]+)(?![A-Za-z0-9_.])"
        ),
        r"(?<![A-Za-z0-9_'!?])(?:(?:IO|BaseIO)\s+UInt32|Ending|CallEnd)(?![A-Za-z0-9_'!?])",
        {},
    ),
]


# The modules of this library outside OnBytes/ that may lie below the root.
BELOW = [
    'Fmt.Blake2b',
    'Fmt.Blake2bFast',
    'Fmt.FieldE',
    'Fmt.M1View',
    'Fmt.ParamsRead',
    'Fmt.Plan',
    'Fmt.Rules1',
    'Fmt.Rules23',
    'Fmt.Rules4',
    'Fmt.Rules5',
    'Fmt.Rules5Fast',
    'Fmt.Rules6',
    'Fmt.Rules6Laws',
    'Fmt.Rules6Round',
    'Fmt.Rules7',
    'Fmt.Rules8',
    'Fmt.Rules8Fast',
    'Fmt.Rules8More',
    'Fmt.Rules8X',
    'Fmt.Toy1',
    'Fmt.Toy1Files',
    'Fmt.View',
    'Run.Blake2b.Compress',
    'Run.Blake2b.Hash',
    'Run.Blake2b.HashThm',
    'Run.Blake2b.LoadThm',
    'Run.Blake2b.ResumeThm',
    'Run.Blake2b.Salted',
    'Run.Blake2b.SaltedPlain',
    'Run.Blake2b.SaltedThm',
    'Run.Blake2b.Spec',
    'Run.Blake2b.SpecFast',
    'Run.Blake2b.WordsThm',
]


def below(*roots):
    """Returns (the modules of this library that the roots import, directly or through others, the
    roots included, each with its text; a message for each of them whose header cannot be read).
    Imports are read as in the step "imports". An import that is not one of the library's files is
    skipped: the step "tree" rejects it."""
    have, seen, todo, odd = set(FILES), {}, list(roots), []
    while todo:
        m = todo.pop()
        if m in seen or lclib.rel_of(m) not in have:
            continue
        seen[m] = text(lclib.rel_of(m))
        try:
            todo += lclib.imports_of(seen[m])
        except ValueError as e:
            odd.append('%s: its header cannot be read: %s' % (lclib.rel_of(m), e))
    return seen, odd


# A line that begins, after attributes and modifiers, with a word that opens a declaration or
# another command. "where" is among them: what follows it are declarations of their own.
COMMAND_RX = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|meta|noncomputable|unsafe|partial|nonrec|"
    r"local|scoped(?:\[[^\]\n]*\])?)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|example|structure|class|inductive|opaque|axiom|mutual|"
    r"where|namespace|section|end|open|export|set_option|attribute|variable|universe|deriving|"
    r"initialize|builtin_initialize|macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|"
    r"postfix|elab|elab_rules|alias|irreducible_def|omit|include|recall|add_decl_doc|unif_hint)"
    r"(?![A-Za-z0-9_'!?])"
)


def below_root(root):
    """Three verdicts of the step "words" on the modules below root, the root module of a program.
    The first: every header can be read, and PROGRAM_RX (commands that program Lean) matches only
    in lines that scan-exceptions.txt allows. The second: each match of a pattern of ENDS, in the
    modules that its entry picks, lies in a definition that the entry lists for that file. The
    third: every module outside the root's top-level directory is listed in BELOW. All three fail if
    root is no file of this library.
    scripts/RULES.txt, "The program's source" and "The program's outcome"."""
    mods, hits = below(root)
    said, looked = [], [0] * len(ENDS)
    for m in sorted(mods):
        rel = lclib.rel_of(m)
        code = code_of(mods[m], strings=True).replace('\u00ab', ' ').replace('\u00bb', ' ')
        hits += ['%s:%d: %s%s' % ((rel,) + p) for p in two_looks(rel, mods[m], PROGRAM_RX, True)]
        # cur: the definition that contains the current line: from an unindented line "def NAME"
        # (attributes, private and protected may precede it) to the next unindented line of code
        cur, rows = None, [
            (i, rx, where)
            for i, (_, rx, only, where) in enumerate(ENDS)
            if only is None or re.search(only, code)
        ]
        curs = []
        for l in code.split('\n'):
            d = re.match(
                (r'\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|' r'protected)\s+)*def\s+([^\s:({\[]+)'), l
            )
            if l[:1].strip() or d or COMMAND_RX.match(l):
                # an indented "def", or any other indented line that begins like a declaration or a
                # command, ends the definition above it and begins none that counts
                cur = d.group(1) if d and l[:1].strip() else None
            curs.append(cur)
        # the patterns are searched in the whole text, so a match may span a line break; it is
        # judged by the definition in which it begins
        for _, rx, where in rows:
            for x in re.finditer(rx, code):
                k = code.count('\n', 0, x.start()) + 1
                if curs[k - 1] not in where.get(rel, ()):
                    said.append('%s:%d: %s' % (rel, k, ' '.join(x.group(0).split())))
        for i, _, _ in rows:
            looked[i] += 1
    for ls, t in (
        (
            hits,
            (
                '%d modules of this library; %d places where a command programs '
                'Lean (scripts/RULES.txt, "The program\'s source")'
            )
            % (len(mods), len(hits)),
        ),
        (
            said,
            (
                '%d places where the outcome of a run is decided outside the '
                'definitions meant for it (scripts/RULES.txt, "The program\'s outcome"). %s'
            )
            % (
                len(said),
                '; '.join(
                    '%s: only in %s; searched in %d modules'
                    % (
                        n,
                        ', '.join(
                            sorted(d for f, v in w.items() if lclib.mod_of(f) in mods for d in v)
                        )
                        or 'no definition',
                        looked[i],
                    )
                    for i, (n, _, _, w) in enumerate(ENDS)
                ),
            ),
        ),
    ):
        for h in ls[:60]:
            print('   ' + h)
        if len(ls) > 60:
            print('   ... and %d more' % (len(ls) - 60))
        if ls:
            print(
                '   (If a place above is legitimate, do not reword it to get '
                'past this step: tell the maintainers of check.py.)'
            )
        verdict(
            'words',
            not ls and bool(mods),
            'below %s: %s' % (root, t) if mods else '%s is not a file of this library' % root,
        )
    own = root.split('.')[0] + '.'
    more = [m for m in sorted(mods) if not m.startswith(own) and m not in BELOW]
    for m in more[:60]:
        print('   %s lies below the root and is not listed in BELOW in check.py' % lclib.rel_of(m))
    verdict(
        'words',
        not more and bool(mods),
        (
            'below %s: %d modules of this library outside %s, all among the %d that BELOW lists'
            % (root, len([m for m in mods if not m.startswith(own)]), own[:-1] + '/', len(BELOW))
            if not more
            else 'below %s: %d modules that BELOW in check.py does not list (scripts/RULES.txt, '
            '"The program\'s source")' % (root, len(more))
        ),
    )


# THE PROGRAM'S GUARDS: the guards themselves are in place (GUARDS, ENTRY, GUARD_REACH, GUARD_SUMS).
# scripts/RULES.txt, "The program's guards". After changing a guard, put its new sha256 into
# GUARD_SUMS.
REMAKE_RX = re.compile(
    r"(?:macro_rules|syntax|elab_rules|command_elab|macro|" r"elab)(?![A-Za-z0-9_'!?])"
)
GUARDS = {
    'OnBytes/Guard/Program.lean': [
        'import OnBytes.Guard.Core',
        'import OnBytes.Main',
        'set_option autoImplicit false',
        'namespace OnBytes.Guard',
        'theorem main_eq : _root_.main = OnBytes.Shell.programFront := rfl',
        'end OnBytes.Guard',
        '#print axioms OnBytes.Guard.main_eq',
        '#guard_csimp [] 0',
        '#guard_cone [``main] []',
        '#guard_pinned [``main] []',
        '#guard_compiled [``main] []',
        '#guard_core [``main] OnBytes.Guard.coreOfProgram',
        '#guard_has [``main] OnBytes.Guard.judges',
        '#guard_entry ``main ``OnBytes.Shell.programFront',
        '#guard_twins "_unsafe_rec" "partial" 1',
        '#guard_tables [``Lean.regularInitAttr, ``Lean.builtinInitAttr, ``Lean.exportAttr,',
        '  ``Lean.Compiler.implementedByAttr, ``Lean.externAttr] []',
        '#guard_ctors [``main] ``IO.FS.Mode [``IO.FS.Mode.read]',
        '#guard_parts ["_boxed", "_closed_", "_lam_", "_elam", "_at_", "_redArg"]',
        '#guard_homes []',
        '#guard_rings [``main] OnBytes.Guard.ringsOfProgram',
        '#guard_imports `OnBytes.Main OnBytes.Guard.barredOfProgram',
        '#guard_plain `OnBytes.Main "_unsafe_rec" []',
    ],
}
ENTRY = {
    'OnBytes/Main.lean': [
        'import OnBytes.Shell.Front',
        'def main (args : List String) : IO UInt32 := OnBytes.Shell.programFront args',
    ],
}  # not a guard file: the program's root, which a guard checks
# compared as whole files; a file of GUARDS not listed here need only end with its lines
WHOLE = ['OnBytes/Guard/Program.lean', 'OnBytes/Main.lean']
GUARD_REACH = {'OnBytes.Guard.Program': ['OnBytes.Main', 'OnBytes.Guard.Core', 'OnBytes.Guard.Cmd']}
# The sha256 of these files' bytes. The root and the guard file are also compared line by line, with
# comments blanked by code_of, and a definition could be hidden next to these lines; a checksum
# misses nothing. The lines stay above, for the reader. One line for each file: the sum, the path.
# PINS: BEGIN
GUARD_SUMS_TEXT = """
ec58568dcbf6a442adfc869d7c7ece4b60551615f19651fdec81f7f74fc2aa32 OnBytes/Guard/Program.lean
29b4b22e88ae7cd49443fea81e182fa5bc9be12355521d64f3c0e2e74f12c572 OnBytes/Main.lean
d39c6cfb209af4d41995e40e7428c14165912302127f85c07389442d64efc46c OnBytes/Guard/Allow.lean
19cdbd97a4f32c9b14345d43596571146e3d537a0bb38cee4cb8d3ad3cc75d28 OnBytes/Guard/Basic.lean
dc9dd4f8f6920ef7e0bc8c5eb2ea37d37e361fcb818b26ead6e3c99d86582a0a OnBytes/Guard/Cmd.lean
4ca404088c37eb83ef2d04c113eae9c5c7e903e9543a4c6785bb23f8dd42dd81 OnBytes/Guard/Cone.lean
e4c49fc1b80e3b0148b00bb1b35f084996edc0916f9ef4408e30bfe23b057358 OnBytes/Guard/Core.lean
3bde8a1a525a0934f8683e82d0a82f2769312aff87ea84f7a4a2b7e8aea269b8 OnBytes/Guard/Csimp.lean
e9042a83af0c574f828c416214c7db32e801424834a3e1aefdf1ab44de7bbbcb OnBytes/Guard/Test.lean
7ef6754b8cb3b5b6374df0228a30c064b7dd4f3c1b5c0e22682a822d5861410e OnBytes/Shell/Checks.lean
63ca7d107b513e643a0cad1140212dab99e39ba963b839cb275496630407a460 OnBytes/Shell/Front.lean
7ffc52a996cc981f3b8badd9d9271fa5503bb9f031952f5d8582f1c37e838c4f OnBytes/Shell/FrontSame.lean
e1f1a47cba0ba3e4efe987173249f560eb82813d64d830517617fe79080ce3ff OnBytes/Shell/TestNames.lean
f5ca0fcf69954e2fec6a8c708c46f34909588ea309d4d5b067ec1de50c974678 Run/Blake2b/LoadThm.lean
"""
# PINS: END
pin_shape('GUARD_SUMS_TEXT', GUARD_SUMS_TEXT)
GUARD_SUMS = {l.split()[1]: l.split()[0] for l in GUARD_SUMS_TEXT.split('\n') if l}


def guards_stand():
    """A verdict of the step "words": the program's guards are in place. Each file of GUARDS and
    ENTRY, without its comments, ends with the stored lines, or consists of them if it is in WHOLE;
    each module of GUARD_REACH reaches the modules named with it; each file of GUARD_SUMS has its
    sha256; in the modules that the files of GUARDS import or reach, those of GUARD_SUMS apart,
    every header can be read and REMAKE_RX (six words that make new syntax or commands) matches only
    in lines that scan-exceptions.txt allows. scripts/RULES.txt, "The program's guards"."""
    bad = [
        '%s is not a file of this library' % f
        for f in list(GUARD_SUMS)
        + [lclib.rel_of(t) for t in GUARD_REACH if lclib.rel_of(t) not in GUARD_SUMS]
        + list(ENTRY)
        if f not in FILES
    ]
    for f, want in list(GUARDS.items()) + list(ENTRY.items()):
        # strings are kept: some arguments of the guard commands are strings, and they are compared
        # character by character too
        got = (
            [l.rstrip() for l in code_of(text(f), strings=True).split('\n') if l.strip()]
            if f in FILES
            else None
        )
        if got is not None and (got if f in WHOLE else got[-len(want) :]) != want:
            bad.append(
                (
                    (
                        '%s, without its comments, is not exactly these %d lines, '
                        'including indentation: %s'
                    )
                    if f in WHOLE
                    else ('%s does not end with these %d lines, each without indentation: ' '%s')
                )
                % (f, len(want), ' | '.join(want))
            )
    for t, reach in GUARD_REACH.items():
        top, odd = below(t)
        bad += odd + ['%s does not reach %s by its imports' % (t, m) for m in reach if m not in top]
    for f, want in GUARD_SUMS.items():
        if f in FILES and lclib.sha(open(ROOT + '/' + f, 'rb').read()) != want:
            bad.append(
                (
                    '%s has the sha256 %s; this check.py expects %s (if the guard '
                    'was changed on purpose, put the new sha256 into GUARD_SUMS in '
                    'check.py, in the same change)'
                )
                % (f, lclib.sha(open(ROOT + '/' + f, 'rb').read()), want)
            )
    under, odd = below(*[lclib.mod_of(f) for f in GUARDS])
    bad += odd
    for m in sorted(under):
        if lclib.rel_of(m) in GUARD_SUMS:
            continue
        bad += [
            (
                '%s:%d: %s (rejected in every module that a guard\'s file '
                'imports: scripts/RULES.txt, "The program\'s guards", (d))%s'
            )
            % ((lclib.rel_of(m),) + p)
            for p in two_looks(lclib.rel_of(m), under[m], REMAKE_RX, True)
        ]
    for b in bad[:60]:
        print('   ' + b)
    if len(bad) > 60:
        print('   ... and %d more' % (len(bad) - 60))
    verdict(
        'words',
        not bad,
        (
            'the guards: checked: %d commands in %s (files compared line by '
            'line as a whole: %d of %d), and the program\'s root; that %s; '
            'the sha256 of %d files; that none of the %d other modules which '
            'they import defines a new command; %d problems (scripts/RULES.txt, '
            '"The program\'s guards")'
        )
        % (
            sum(l.startswith('#guard_') for v in GUARDS.values() for l in v),
            ', '.join(GUARDS),
            sum(f in WHOLE for f in GUARDS),
            len(GUARDS),
            '; that '.join('%s reaches %s' % (t, ', '.join(r)) for t, r in GUARD_REACH.items()),
            len(GUARD_SUMS),
            len([m for m in under if lclib.rel_of(m) not in GUARD_SUMS]),
            len(bad),
        ),
    )


# THE GOALS' FILES: Ladder.lean states the goals at the top of this library, and three files beside
# it hold its stored terms, its tests and its ties; Ladder/Bits.lean and Ladder/Package.lean state
# further goals. Pinned with them: four files of Ladder/ with theorems between the goals and from
# them to the statements, and eleven files of VerifiableInference/: the statements that the goals
# apply, the definitions that these are written in, and theorems that tie these definitions to the
# library's own (Bridge.lean, Deterministic.lean, OfArgument.lean). Seven more state goals too: the
# three files of VerifiableInference/ in which two goals are written (AtEveryRequest.lean,
# RequestResult.lean, WellFormedRequests.lean), AtEveryRequestGuards.lean, and the three files of
# Johnson/Face/ that define the lines of the final statement. One more states the six final lines:
# AtFullSide/Face/TheSixLines.lean. Their text is fixed: every byte is pinned, comments too, because
# the limits of the goals stand in comments. This pins these twenty-nine files and nothing beneath
# them, nor the other files of the four directories: a definition of the library that a goal names
# can change, and the goal's meaning with it, without a failure here. One line for each file: the
# sum, the path.
# PINS: BEGIN
GOAL_SUMS_TEXT = """
c3b6765b2feb504787681c16c58f4521c28c599a4a502cfddd5a3c324b3dd3d3 Ladder.lean
beb03140b42c2d92d7d9857ef560d3c4fbbe6d27c2f28edfd931af07180b5e0f Ladder/Bits.lean
df2f55f7f7dc07a9a8eeb442d3e8de89466f367d7ee4d8eeaf7e41232f21cf71 Ladder/Guards.lean
d24b5666dfc8dc9fddf2105f1e6ac4df0ef703c960563c376fe4156a50a93548 Ladder/Package.lean
f0b33ae1e4e714e4421bd3a5ccb7239da1dce0e0296458e38915f46ef464c887 Ladder/Stored.lean
6c88d83fa8edba384502d4b8708cada918a92aeee502ea4f4a63a860bf909433 Ladder/Ties.lean
34886ad4f01172221712480735d0a81d18fc11be401aaf11b3fa5ff1a1708dd6 Ladder/BitsTies.lean
5b1222744b521b735e076142b93e898011255b04ccfa7ce9b19a946a7b8a32fd Ladder/NonEmptyTies.lean
538d071f609cc560f762029e02ae9d8bef6ad4d444114456b5acd544d56b6e6d Ladder/PackageBits.lean
2b2a6edf48e9043e0c78cd2e1e269122c5914cd657228099396ff354b5f5650c Ladder/PackageTies.lean
ef3032941ec893e23b552ad8c1bc51ecc5ccf58bd95932e47704abdfc3a7db7c VerifiableInference/Bridge.lean
f33ed6fab0f60e38ed22f3f80a06e59e3631d89dc524d3b42a880b7a5d3aa074 VerifiableInference/CanServe.lean
bc6c2225335b4d19278ab8523bdb70cae68fdcb9629edb309d93b7acb0fa99fe VerifiableInference/Deterministic.lean
8a01031138552eaa5f0ca2c3b94df85040d3999e2cccd890e5c495cfc012da3c VerifiableInference/ModelWeights.lean
d3135fa09865d0907ecb2a7f91247970d3991105a4bab2e605bebd162602c66a VerifiableInference/MoreStatements.lean
372f4e089195db8a2f703c4889b62d974019c7485b4e58d0e9aebee800e887a8 VerifiableInference/OfArgument.lean
da6b53ff406ae95380e3a991c414250320303eb7baa56c0e47b5a5e8946555cd VerifiableInference/RandomOracleModel.lean
c9250f45987e58a0720060dc400d069efe4025b3976f98f689c19d713db59ead VerifiableInference/Statements.lean
05dc8a42eb9b013b67a99783a94ea3c038c4757f5483d363aff7e2f513940b29 VerifiableInference/StatementsNonEmpty.lean
f8848a4afed5456d2c15503897c05f31f91a3fb2ee11c27cbefc85a74a90b617 VerifiableInference/Steps.lean
86d9d0444a893e2debaac462790699ed78a505d4dd0ac5e3a87190110db558dd VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean
b037ad987f3681a3a3a0fd7e8e9237beb6175fe78956003db5cba4f2537d5b8c VerifiableInference/AtEveryRequest.lean
bafab05ddb1bc933eea36de9442d5f75ad44cb96558c97a525cf2300ef547768 VerifiableInference/AtEveryRequestGuards.lean
7d5788aa01fdd332982965a3d5f5ca7c6c169b1deed88cdb79d5f2690c080462 VerifiableInference/RequestResult.lean
65ca61e7922e0e0e5f2fb300bd201b9b5349abef319af0016266f6ac983d3ff0 VerifiableInference/WellFormedRequests.lean
70b08e504d06ee829ef84ddd1047da3237c86abd684465a1057080c8e028aca0 Johnson/Face/Checks.lean
1407411a57c7d87eb32f7f054f4542684b3bcd7bc4772e01c3538343bace6b4a Johnson/Face/FinalStatement.lean
6f0b1a87f3315057958728817bd8f0f44a9b1609e08591b520c9d4555e24ffbe Johnson/Face/FinalStatementOneBit.lean
dcec65cb770e3ea09e125efb9bf712bb64949806162fb77377ec3e3802066b2f AtFullSide/Face/TheSixLines.lean
"""
# PINS: END
pin_shape('GOAL_SUMS_TEXT', GOAL_SUMS_TEXT)
GOAL_SUMS = {l.split()[1]: l.split()[0] for l in GOAL_SUMS_TEXT.split('\n') if l}


def goals_stand():
    """A verdict of the step "words": each file of GOAL_SUMS is a file of this library, and its
    bytes have the sha256 stored there."""
    bad = ['%s is not a file of this library' % f for f in GOAL_SUMS if f not in FILES]
    for f, want in GOAL_SUMS.items():
        if f in FILES and lclib.sha(open(ROOT + '/' + f, 'rb').read()) != want:
            bad.append(
                '%s has the sha256 %s; this check.py expects %s (the text of the goals is fixed: '
                'if the file was changed on purpose, and whoever may allow that has allowed it, '
                'put the new sha256 into GOAL_SUMS_TEXT in check.py, in a change of its own)'
                % (f, lclib.sha(open(ROOT + '/' + f, 'rb').read()), want)
            )
    for b in bad:
        print('   ' + b)
    verdict(
        'words',
        not bad,
        'the goals\' files: the %d files of GOAL_SUMS (Ladder.lean and those with it) are the '
        'stored ones, byte for byte; what lies beneath the goals in the library is not pinned: '
        '%d faults' % (len(GOAL_SUMS), len(bad)),
    )


# NO_ROWS: the theorems that claimed-theorems.tsv may mark "no": scripts/RULES.txt, "The named
# theorems".
# PINS: BEGIN
NO_ROWS = [
    'TopC.level_arith',
    'TopC.Val2.level_pow',
    'TopC.ver_inv8',
    'Code.Lines.coeff_swap',
    'Compile.three_sum_range_le',
    'Prob.ref_entry',
    'Prob.ref_exponent',
]
# PINS: END
pin_shape('NO_ROWS', NO_ROWS)


def claimed_stand():
    """A verdict of the step "words" on scripts/claimed-theorems.tsv: the list has lines; every line
    can be read and names a file of this library; a name with "yes" is on a line of
    top-theorems.txt; a name with "no: .." is listed in NO_ROWS, is on no line of top-theorems.txt,
    and its file has an unindented line that begins with "theorem" and then the full name or a final
    part of it."""
    rows = {l.split()[0] for l in data('top-theorems.txt')}
    bad, nos = [], 0
    lines = data('claimed-theorems.tsv')
    if not lines:
        bad.append('scripts/claimed-theorems.tsv is absent or has no line')
    for l in lines:
        p = l.split('\t')
        if (
            len(p) < 5
            or not p[1].startswith('lean/')
            or not (p[4] == 'yes' or (p[4].startswith('no: ') and p[4][4:].strip()))
        ):
            bad.append(
                (
                    'claimed-theorems.tsv: this line cannot be read: "%s". A line '
                    'has these fields, separated by tabs: the full name; its file '
                    '("lean/.."); two fields that check.py does not read; then '
                    '"yes", or "no: " and a reason'
                )
                % l[:80]
            )
            continue
        n, f = p[0], p[1][5:]
        if f not in FILES:
            bad.append('%s: its file %s is not a file of this library' % (n, f))
            continue
        if p[4] == 'yes':
            if n not in rows:
                bad.append(
                    ('%s is on no line of top-theorems.txt, so the audit would not ' 'look for it')
                    % n
                )
            continue
        nos += 1
        parts = n.split('.')
        code = code_of(text(f))
        if n not in NO_ROWS:
            bad.append(
                (
                    '%s: claimed-theorems.tsv says "no", but NO_ROWS in check.py '
                    'does not list it among the theorems that the audit cannot check'
                )
                % n
            )
        if n in rows:
            bad.append(
                (
                    '%s: claimed-theorems.tsv says that the audit cannot check it, '
                    'but top-theorems.txt names it'
                )
                % n
            )
        if not any(
            re.search(
                r'(?m)^theorem\s+%s(?![A-Za-z0-9_\'!?.])' % re.escape('.'.join(parts[k:])), code
            )
            for k in range(len(parts))
        ):
            bad.append(
                ('%s: %s has no unindented line "theorem .." that ends with this ' 'name') % (n, f)
            )
    for b in bad[:60]:
        print('   ' + b)
    if len(bad) > 60:
        print('   ... and %d more' % (len(bad) - 60))
    verdict(
        'words',
        not bad and bool(lines),
        (
            (
                'the named theorems: %d lines of '
                'claimed-theorems.tsv, %d of them on no line of top-theorems.txt, each '
                'with its reason; %d problems'
            )
            % (len(lines), nos, len(bad))
            if lines
            else 'claimed-theorems.tsv is absent or has no line'
        ),
    )


# PINS: BEGIN
GUARDS_SUM = 'eccabe42ac216d068c88f1e0e97299a25292303568468590c4ff09c44afd6b87'
# PINS: END
pin_shape('GUARDS_SUM', GUARDS_SUM)
# How many lines of each kind scripts/top-theorems.txt has. Only on a closed line or a headline does
# the audit give a verdict on binders and on Classical.choice: a list from which such lines have
# been taken, or in which they have been made general, would pass with fewer verdicts.
# PINS: BEGIN
KINDS = {'closed': 0, 'headline': 0, 'general': 10776}
# PINS: END
pin_shape('KINDS', KINDS)
# PINS: BEGIN
STATEMENTS_SUM = '377e116300856e6c762386931e030eee0288e53b12105d2f8ac34b61ebd1c61d'
# PINS: END
pin_shape('STATEMENTS_SUM', STATEMENTS_SUM)


def kinds_pinned():
    """A verdict of the step "words": top-theorems.txt has the numbers of lines that KINDS says."""
    have = {'closed': 0, 'headline': 0, 'general': 0}
    for l in data('top-theorems.txt'):
        w = l.split()[1:2]
        have[w[0] if w in (['headline'], ['general']) else 'closed'] += 1
    say = lambda d: ', '.join('%d %s' % (d[k], k) for k in ('closed', 'headline', 'general'))
    verdict(
        'words',
        have == KINDS,
        'the lines of top-theorems.txt by kind: %s%s'
        % (
            say(have),
            (
                ''
                if have == KINDS
                else '; this check.py expects %s (if the list was changed on purpose, put the new '
                'numbers into KINDS in check.py, in the same change)' % say(KINDS)
            ),
        ),
    )


def statements_in(t):
    """Reads the audit's listing t. Returns, for each theorem that has a block there, its compiled
    statement as the listing prints it and the sha256 of the same statement printed in full, with
    all implicit arguments; or, in place of the pair, a sentence on why the block is not used. A
    printed name can hold line breaks and imitate the listing's own lines. So nothing is read unless
    the listing has one line "statement in full (" and one line "binders after unfolding " for each
    head, and no block is used whose name heads more than one. A block ends at the next "=== "."""
    at = {}
    for m in re.finditer(r'(?m)^=== (\S+)   \[module [^\]\n]*\]$', t):
        at.setdefault(m.group(1), []).append(m.start())
    heads = sum(len(ps) for ps in at.values())
    if not (
        len(re.findall(r'(?m)^statement in full \(', t))
        == len(re.findall(r'(?m)^binders after unfolding ', t))
        == heads
    ):
        return {n: 'the listing does not have its three lines once for each theorem' for n in at}
    out = {}
    for n, ps in at.items():
        if len(ps) > 1:
            out[n] = '%d blocks of the listing have this name' % len(ps)
            continue
        end = t.find('\n=== ', ps[0])
        m = re.match(
            r'(?s)=== \S+   \[module [^\]\n]*\]\nstatement: (.*?)\n'
            r'statement in full \([^)\n]*\): ([^\n]*)\nbinders after unfolding ',
            t[ps[0] : end if end >= 0 else len(t)],
        )
        out[n] = (
            (m.group(1), lclib.sha(m.group(2).encode('utf-8')))
            if m
            else 'its block in the listing cannot be read'
        )
    return out


def statements_pinned(listing):
    """A verdict of the audit. On a general line of top-theorems.txt the audit compares the
    statement with nothing. scripts/front-statements.txt holds the compiled statements of the
    theorems at the front of the library, as an earlier run's listing printed them; here they are
    compared, to the letter, with this run's listing. A block of the file: "=== " and the name;
    "in full: " and a sha256; the statement's lines. Every theorem of claimed-theorems.tsv whose
    file lies in VerifiableInference/, and that NO_ROWS does not name, must have a block.
    STATEMENTS_SUM is the file's own sha256.
    If the verdict fails, the blocks as this run's listing has them are written beside the logs."""
    p, bad = ROOT + '/scripts/front-statements.txt', []
    got = lclib.sha(open(p, 'rb').read()) if os.path.isfile(p) else 'absent'
    if got == 'absent':
        bad.append('scripts/front-statements.txt is absent')
    elif got != STATEMENTS_SUM:
        bad.append(
            'scripts/front-statements.txt has the sha256 %s; this check.py expects %s (if a '
            'statement was changed on purpose, read the new one, then put the new sha256 into '
            'STATEMENTS_SUM in check.py, in the same change)' % (got, STATEMENTS_SUM)
        )
    want = {}
    for b in re.split(r'(?m)^=== ', '\n'.join(data('front-statements.txt')))[1:]:
        ls = b.rstrip('\n').split('\n')
        if ls[0] in want:
            bad.append('front-statements.txt: a second block "=== %s"' % ls[0][:80])
        elif len(ls) < 3 or not re.fullmatch('in full: [0-9a-f]{64}', ls[1]):
            bad.append(
                'front-statements.txt: the block "=== %s" cannot be read (its next line must be '
                '"in full: " and 64 hex digits, and a statement must follow)' % ls[0][:80]
            )
        else:
            want[ls[0]] = ('\n'.join(ls[2:]), ls[1][9:])
    front = [
        p[0]
        for p in (l.split('\t') for l in data('claimed-theorems.tsv'))
        if len(p) > 1 and p[1].startswith('lean/VerifiableInference/') and p[0] not in NO_ROWS
    ]
    bad += [
        '%s, which a document names, lies in VerifiableInference/ and has no block in '
        'front-statements.txt' % n
        for n in front
        if n not in want
    ]
    have = statements_in(listing)
    for n, (s, full) in want.items():
        now = have.get(n)
        if now is None:
            bad.append(
                '%s is not in the listing: is it a line of top-theorems.txt, and a theorem of the '
                'compiled library?' % n
            )
        elif isinstance(now, str):
            bad.append('%s: %s' % (n, now))
        elif now[0] != s:
            a, b = s.split('\n'), now[0].split('\n')
            k = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
            bad.append(
                '%s: its compiled statement is not the one in front-statements.txt; they part at '
                'line %d of the statement' % (n, k + 1)
            )
        elif now[1] != full:
            bad.append(
                '%s: its compiled statement reads the same, but printed in full, with the implicit '
                'arguments, it is not the one whose sha256 front-statements.txt has' % n
            )
    for b in bad[:30]:
        print('   ' + b)
    if len(bad) > 30:
        print('   ... and %d more' % (len(bad) - 30))
    if bad:
        new = [n for n in dict.fromkeys(list(want) + front) if isinstance(have.get(n), tuple)]
        open(fresh('front-statements.now.txt'), 'w', encoding='utf-8', newline='').write(
            ''.join('=== %s\nin full: %s\n%s\n' % (n, have[n][1], have[n][0]) for n in new)
        )
        print(
            '   the blocks of %d theorems as this run\'s listing has them: %s (if a change was '
            'meant: scripts/RULES.txt, "The front\'s compiled statements")'
            % (len(new), OUT + '/front-statements.now.txt')
        )
    verdict(
        'audit',
        not bad and bool(want),
        (
            'the compiled statements of %d theorems are those of front-statements.txt' % len(want)
            if not bad and want
            else (
                '%d problems, listed above; front-statements.txt has %d blocks'
                % (len(bad), len(want))
                if bad
                else 'front-statements.txt has no block'
            )
        ),
    )


def guards_of(rel):
    """Returns how many "#guard" commands the file rel has, and the sha256 of its code. A command is
    counted wherever "#guard" stands at the start of a line or after a blank, in the text with
    comments and literals blanked. The code is the whole text with comments blanked and literals
    kept (the expected values are literals), without trailing blanks and empty lines."""
    t = text(rel)
    n = len(re.findall(r'(?m)(?:^|(?<=[ \t]))#guard', code_of(t)))
    code = [l.rstrip() for l in code_of(t, strings=True).split('\n') if l.strip()]
    return n, lclib.sha('\n'.join(code).encode('utf-8'))


def guards_pinned():
    """A verdict of the step "words". A "#guard" command is a test that Lean evaluates while it
    compiles the file. It leaves no declaration, so if one were taken out or weakened, neither the
    replay nor the audit would notice. scripts/guards.txt lists every file that has such commands:
    the path, how many, the sha256 of the file's code, separated by tabs. The sum covers the whole
    file, because code around a command can weaken it or keep Lean from reaching it. GUARDS_SUM is
    the sha256 of the list itself."""
    pinned, bad = {}, []
    p = ROOT + '/scripts/guards.txt'
    got = lclib.sha(open(p, 'rb').read()) if os.path.isfile(p) else 'absent'
    if got == 'absent':
        bad.append('scripts/guards.txt is absent')
    elif got != GUARDS_SUM:
        bad.append(
            'scripts/guards.txt has the sha256 %s; this check.py expects %s (if the list was '
            'changed on purpose, read the changed files, then put the new sha256 into GUARDS_SUM '
            'in check.py, in the same change)' % (got, GUARDS_SUM)
        )
    for l in data('guards.txt'):
        p = l.split('\t')
        if len(p) != 3 or not re.fullmatch('[0-9]{1,9}', p[1]):
            bad.append('guards.txt: a row that is not "path, count, sha256" with tabs: ' + l[:80])
        elif p[0] in pinned:
            bad.append('guards.txt: a second row for ' + p[0])
        else:
            pinned[p[0]] = (int(p[1]), p[2])
    have = {}
    for rel in FILES:
        if '#guard' in text(rel):
            n, s = guards_of(rel)
            if n:
                have[rel] = (n, s)
    now = 'if the change is deliberate, read it; the row would now be "%s\t%d\t%s"'
    for f, (n, s) in pinned.items():
        if f not in have:
            bad.append(
                '%s has no "#guard" command, or is gone; guards.txt lists %d (if that is '
                'deliberate, remove its row)' % (f, n)
            )
        elif have[f][0] != n:
            bad.append(
                '%s has %d "#guard" commands; guards.txt lists %d (%s)'
                % (f, have[f][0], n, now % ((f,) + have[f]))
            )
        elif have[f][1] != s:
            bad.append(
                '%s: its code is not the code that guards.txt lists (%s)'
                % (f, now % ((f,) + have[f]))
            )
    if got != 'absent':
        bad += [
            '%s has "#guard" commands and no row in guards.txt (%s)' % (f, now % ((f,) + have[f]))
            for f in have
            if f not in pinned
        ]
    for b in bad[:30]:
        print('   ' + b)
    if len(bad) > 30:
        print('   ... and %d more' % (len(bad) - 30))
    verdict(
        'words',
        not bad,
        '"#guard" commands: %d in %d files; guards.txt lists %d in %d files; %d problems'
        % (
            sum(v[0] for v in have.values()),
            len(have),
            sum(v[0] for v in pinned.values()),
            len(pinned),
            len(bad),
        ),
    )


def step_words():
    """The step "words". Its first verdict: ODD_BYTES is empty, and a rejected word stands, in the
    text with comments blanked or (but for sorry, axiom and partial) in the raw text, only in lines
    that scan-exceptions.txt allows (in none, if that list has not the expected sha256). Its last:
    the list has that sha256, no entry that matches no line and none without a reason. Between the
    two it calls below_root for each root, guards_stand, goals_stand, claimed_stand, kinds_pinned
    and guards_pinned."""
    print(
        (
            '== words: text only: none of %s and further names '
            '(scripts/RULES.txt, "Every word is searched twice"), searched in the text '
            'with comments blanked and, except sorry, axiom and partial, in the raw '
            'text too; three rules on the modules below OnBytes.Main; '
            'the named theorems; the "#guard" '
            'commands. A place '
            'marked%s is in what looks like '
            'a comment or a string: if the line is legitimate, it needs an '
            'entry in scripts/scan-exceptions.txt'
        )
        % (', '.join(WORDS), RAW_ONLY),
        flush=True,
    )
    got = (
        lclib.sha(open(ROOT + '/scripts/scan-exceptions.txt', 'rb').read())
        if os.path.isfile(ROOT + '/scripts/scan-exceptions.txt')
        else 'absent'
    )
    # a list with a different sha256 is ignored; otherwise the verdicts printed before the one on
    # the list would be computed under a list supplied by the checked copy
    for l in (data('scan-exceptions.txt') if got == LIST_SUM else []):
        p = l.split('\t')
        if len(p) >= 3 and p[2].strip():
            ex[(p[0], p[1])] = ex.get((p[0], p[1]), 0) + 1
            excode.update({(p[0], p[1])} if p[2].startswith('CODE: ') else ())
        else:
            noreason.append(l)
    # Nothing is required of the character before a word: a digit, a prime, "!", "?" or a letter can
    # end the previous token ("1sorry", "]!extern"). The cost: a name such as my_sorry is reported
    # too. scripts/RULES.txt, "Every word is searched twice".
    hits = list(ODD_BYTES)
    for rel in FILES + ASK:
        raw, one = text(rel), {}
        for n, w, how in two_looks(rel, raw, OLD_RX, False, OLD_RAW_RX):
            one.setdefault(n, (w, how))  # one reported place per line
        hits += [
            '%s:%d: %s: %s%s' % (rel, n, w, raw.split('\n')[n - 1].strip()[:140], how)
            for n, (w, how) in sorted(one.items())
        ]
    for h in hits[:60]:
        print('   ' + h)
    if len(hits) > 60:
        print('   ... and %d more' % (len(hits) - 60))
    verdict(
        'words',
        not hits,
        '%d files read in both searches, %d lines rejected' % (len(FILES + ASK), len(hits)),
    )
    for root in ROOTS:
        below_root(root)
    guards_stand()
    goals_stand()
    claimed_stand()
    kinds_pinned()
    guards_pinned()
    stale = [k for k in ex if used.get(k, 0) < ex[k]]
    for k in stale[:10]:
        print('   an entry that matches no line: %s: %s' % (k[0], k[1][:100]))
    if got != LIST_SUM:
        print(
            (
                '   scripts/scan-exceptions.txt has the sha256 %s; this check.py '
                'expects %s (if the list was changed on purpose, read the new '
                'lines, then put the new sha256 into LIST_SUM in check.py, in '
                'the same change)'
            )
            % (got, LIST_SUM)
        )
    counts['lines allowed by scan-exceptions.txt'] = sum(used.values())
    counts['of them code'] = sum(v for k, v in used.items() if k in excode)
    verdict(
        'words',
        not stale and not noreason and got == LIST_SUM,
        (
            'the list of allowed lines: %d, %d of them as code; %d stale '
            'entries, %d entries without a reason; the list %s the sha256 '
            'that this check.py expects%s'
        )
        % (
            sum(used.values()),
            counts['of them code'],
            sum(ex[k] - used.get(k, 0) for k in stale),
            len(noreason),
            'has' if got == LIST_SUM else 'does NOT have',
            '' if got == LIST_SUM else ', so none of its lines was used',
        ),
    )


def step_imports():
    """IMPORTS.txt states the layering of the library. "Lib : A B": apart from Lean, Mathlib and its
    companion packages, a file of Lib imports only Lib itself, A and B. "Lib/File.lean : M N -K" or
    "Lib/* : M": those files may also import exactly M and N, and may not import K or what is below
    it. "Lib/Dir/* : M.*": those files, and no other file of Lib, may import and reach M and what is
    below it. The lines also apply to what a file reaches through other files of the library: what
    a line allows its files to import, another file of Lib may reach if it reaches such a file and
    that file reaches the module. A line that cannot mean what it seems to say is a fault of the
    list and fails the step: an entry that is no module name, ".*" or "-" where they have no
    meaning, a line for files that hits no file, a "-K" with no module at or below K, an exact name
    at or below an "M.*" of the same library."""
    print(
        (
            '== imports: IMPORTS.txt, for what a file imports directly, and '
            'for what it reaches through other files of this library'
        ),
        flush=True,
    )
    g, bad = graph()
    libs, exc = {}, []
    for l in data('IMPORTS.txt'):
        if ':' not in l:
            bad.append('a line without a colon: ' + l)
            continue
        who, rest = l.split(':', 1)
        who = who.strip()
        rest = rest.split()
        for x in rest:
            core = x[1:] if x.startswith('-') else x
            core = core[:-2] if core.endswith('.*') else core
            if not lclib.NAME.fullmatch(core):
                bad.append(
                    'the entry %s in the line of %s is no module name (with one "-" before it, or '
                    '".*" behind it, and no blank between)' % (x, who)
                )
            elif x.endswith('.*') and ('/' not in who or x.startswith('-')):
                bad.append(
                    'the entry %s in the line of %s: ".*" has a meaning only in an entry without a '
                    'minus, in a line for files; "-M" and "Lib : M" hold for what is below M '
                    'as well' % (x, who)
                )
            elif x.startswith('-') and '/' not in who:
                bad.append(
                    'the entry %s in the line of %s: a minus has a meaning only in a line for files'
                    % (x, who)
                )
        if '/' in who:
            exc.append(
                (
                    who,
                    [x for x in rest if not x.startswith('-')],
                    [x[1:] for x in rest if x.startswith('-')],
                )
            )
        elif who in libs:
            bad.append(
                ('the library %s has two lines: the second would silently replace ' 'the first')
                % who
            )
        else:
            libs[who] = rest

    def hits(pat, m):
        rel = lclib.rel_of(m)
        return rel == pat or (pat.endswith('/*') and rel.startswith(pat[:-1]))

    def closure(m):
        seen, todo = {}, [(j, [m, j]) for j in g[m]]
        while todo:
            x, path = todo.pop()
            if x in seen:
                continue
            seen[x] = path
            for j in g.get(x, []):
                todo.append((j, path + [j]))
        return seen

    stars = [(q, y) for q, bd, _ in exc for y in bd if y.endswith('.*')]
    for p, ad, rm in exc:
        if not any(hits(p, m) for m in g):
            bad.append('the line of %s hits no file: it allows nothing and bars nothing' % p)
        for r in rm:
            if not any(under(m, r) for m in g):
                bad.append(
                    'the entry -%s in the line of %s: there is no module %s and none below that '
                    'name: it bars nothing' % (r, p, r)
                )
        for x in ad:
            for q, y in stars:
                if (
                    not x.endswith('.*')
                    and q.split('/')[0] == p.split('/')[0]
                    and under(x, y[:-2])
                ):
                    bad.append(
                        'the entry %s in the line of %s: the line of %s keeps %s to its own files, '
                        'and an exact name would let other files of the library reach that module'
                        % (x, p, q, y)
                    )
    lined = {}
    for f in g:
        ad = {x for p, a, _ in exc if hits(p, f) for x in a if not x.endswith('.*')}
        if ad:
            lined[f] = ad
    reach = {f: set(closure(f)) for f in lined}
    for m in sorted(g):
        L = m.split('.')[0]
        if L not in libs:
            bad.append('%s: the library %s has no line in IMPORTS.txt' % (m, L))
            continue
        adds = {x for p, ad, _ in exc if hits(p, m) for x in ad}
        rem = [x for p, _, rm in exc if hits(p, m) for x in rm]
        # what a single-file line allows a file of a library to import, the library's other files
        # may reach only through that file: they reach the file, and the file reaches the module
        # (that they reach the module by no other road as well is not checked)
        cl = closure(m)
        fadds = {
            x
            for f, ad in lined.items()
            if f.split('.')[0] == L and (f == m or f in cl)
            for x in ad
            if x in reach[f]
        }
        # an entry of a single-file line allows exactly that module, not the modules below its name;
        # an entry "M.*" allows M and the modules below its name, and only to the files of its own
        # line: the library's other files may neither import nor reach them
        wide = [x[:-2] for x in adds if x.endswith('.*')]
        okd = lambda j: any(under(j, p) for p in [L] + libs[L] + wide) or j in adds
        okf = lambda j: any(under(j, p) for p in [L] + libs[L] + wide) or j in fadds
        for j in g[m]:
            if j.split('.')[0] in lclib.PACKAGE_ROOTS:
                continue
            if any(under(j, r) for r in rem):
                bad.append(
                    '%s imports %s, which its own line forbids (-%s)' % (m, j, ' -'.join(rem))
                )
            elif not okd(j):
                bad.append(
                    '%s imports %s; allowed: %s' % (m, j, ' '.join([L] + libs[L] + sorted(adds)))
                )
        for x, path in sorted(cl.items()):
            if x.split('.')[0] in lclib.PACKAGE_ROOTS or len(path) == 2:
                continue
            if any(under(x, r) for r in rem) or not okf(x):
                bad.append(
                    (
                        '%s reaches %s: %s   [indirect: IMPORTS.txt is read as a rule on '
                        'what a file reaches, not only on what it imports; README.md]'
                    )
                    % (m, x, ' > '.join(path))
                )
    for b in bad[:40]:
        print('   ' + b)
    if len(bad) > 40:
        print('   ... and %d more' % (len(bad) - 40))
    idle = [L for L in libs if not any(m.split('.')[0] == L for m in g)]
    if idle:
        print('   (no file under: %s)' % ' '.join(idle))
    verdict(
        'imports',
        not bad and bool(libs),
        (
            '%d modules, %d libraries, %d lines for single files; %d rejected'
            % (len(g), len(libs), len(exc), len(bad))
            if libs
            else 'IMPORTS.txt names no library'
        ),
    )


def step_build():
    """Compiles every file, then runs the kernel replay, then the audit, which sees exactly the
    compiled files of this run. The three are run one after the other by Lake. The audit's lines
    carry a random value generated for this run (nonce; one message calls it "the random tag"),
    so that no line printed by a file of the library can pass for one of the audit's."""
    print(
        (
            '== build, kernel replay, audit: on the same compiled files; '
            'every file is compiled in this run'
        ),
        flush=True,
    )
    named = list(FILES)
    left_out = [r for r in THIRD_ONLY if r not in FILES]
    for r in left_out:
        print('   LEFT OUT: %s is not in the copy, so nothing compiles it' % r)
    q = lambda n: '\x60' + n
    nonce = secrets.token_hex(12)
    if SHARED and not a.i_trust_every_account_on_this_machine:
        print(
            '   check.py: the scratch directory %s lies below %s, which another account may be '
            'able to change (%s): it could put another folder in the scratch directory\'s place '
            'while the build '
            'runs and choose what Lean compiles and runs as you. Name a new scratch directory '
            '(CHECK_SCRATCH_DIR) below folders that only you or root can change (such as one in '
            'your home folder, or in /tmp, whose sticky bit keeps others from replacing it), %sor, '
            'if you trust every account on this machine, say so with '
            '--i-trust-every-account-on-this-machine; nothing was built'
            % (
                (OUT,)
                + SHARED
                + (
                    (
                        ''
                        if os.geteuid() == 0
                        else 'or, if %s is yours, close it ("chmod go-w" on it is enough), '
                        % SHARED[0]
                    ),
                )
            )
        )
        for s in ('build', 'replay', 'audit'):
            verdict(s, False, s + ' not run: another account could exchange the scratch directory')
        return
    if LAKE_STOP:
        for x in LAKE_STOP:
            print('   ' + x)
        for s in ('build', 'replay', 'audit'):
            verdict(
                s,
                False,
                s
                + ' not run: Lake is not called '
                + (
                    'where the packages are reached through a link'
                    if len(LAKE_STOP) == len(PACKAGES_LINKED)
                    else 'under these Lake files'
                ),
            )
        return
    if short_of('the largest process of "lake build"', BUILD_GIB) or short_of(
        'the audit, at the end of the step "build"%s,'
        % (' (with --jobs 1 it needs about 7 GiB)' if SIDE > 1 else ''),
        AUDIT_GIB,
    ):
        for s in ('build', 'replay', 'audit'):
            verdict(s, False, s + ' not run: too little memory is free')
        return
    pf = packages_fault()
    if not pf:
        try:
            lake_project(ROOT)
        except (shutil.Error, OSError) as e:
            pf = 'the library\'s .lake/packages could not be copied: %s' % plain(str(e)[:300])
    if pf:
        print('   ' + pf)
        for s in ('build', 'replay', 'audit'):
            verdict(
                s,
                False,
                s + (' not run: Lake is not called without a complete copy of the ' 'packages'),
            )
        return
    control = panic_control()
    # Every Lean file of the library must be compiled. A file that "lake build" does not build
    # (nothing imports it, and no target in BUILD_TARGETS covers it) fails the verdict on the
    # build. If "lake build" itself ended without an error, replay and audit go on without it.
    lrc, unbuilt, lsorry, build_panics = lake_build(named)
    named = [r for r in named if r not in unbuilt]
    if unbuilt:
        print(
            '   Not compiled: "lake build" left no compiled file for %d library files (%s): %s'
            % (
                len(unbuilt),
                (
                    'does one of the libraries that this script names to Lake cover them?'
                    if lrc == 0
                    else 'see the errors of "lake build" in the log'
                ),
                ' '.join(unbuilt[:30])
                + (' ... and %d more' % (len(unbuilt) - 30) if unbuilt[30:] else ''),
            )
        )
        counts[
            'library files that "lake build" did not compile (the verdict on the build fails)'
        ] = len(unbuilt)
    mods = sorted(lclib.mod_of(r) for r in named)
    okname = re.compile(r'[A-Za-z_][A-Za-z0-9_\'!?]*(\.[A-Za-z_][A-Za-z0-9_\'!?]*)*')
    bad = []
    tops, heads = [], []
    for l in data('top-theorems.txt'):
        p = l.split()
        # a headline with named binders: the line spells out the form of the statement
        if len(p) > 1 and p[1] == 'headline' and okname.fullmatch(p[0]):
            h = read_headline(l, okname)
            if isinstance(h, str):
                bad.append('top-theorems.txt: the headline %s: %s' % (p[0], h))
            else:
                heads.append(h)
        elif len(p) == 2 and p[1] == 'general' and okname.fullmatch(p[0]):
            # a general theorem: statement, reach and syntax are reported; no verdict on binders, no
            # limit, no scheme
            tops.append((p[0], None, []))
        elif (
            len(p) > 1
            and (p[1] == '-' or p[1].isdigit())
            and all(okname.fullmatch(x) for x in [p[0]] + p[2:])
        ):
            tops.append((p[0], 0 if p[1] == '-' else int(p[1]), p[2:]))  # "-": no limit
        else:
            bad.append(
                (
                    'top-theorems.txt: cannot read "%s". A line is: the theorem\'s '
                    'full name; "-", or a limit for what it promises; then the '
                    'closed constant(s) that are its scheme. Or: the name, then the '
                    'word general. Or: the name, then the word headline and the form '
                    'of the statement (see the top of top-theorems.txt)'
                )
                % l[:80]
            )
    allow = []
    for l in data('choice-allow.txt'):
        m = re.fullmatch(r'(\S+)\s*>\s*(\S+)\s+(\S.*)', l)
        if m and okname.fullmatch(m.group(1)) and okname.fullmatch(m.group(2)):
            allow.append((m.group(1), m.group(2)))
        else:
            bad.append(
                (
                    'choice-allow.txt: cannot read "%s". The form is  A > B  reason  '
                    '(the walk does not go from A to B); the reason is required'
                )
                % l[:80]
            )
    every = [x for x, _, _ in tops] + [h[0] for h in heads]
    for n in sorted({x for x in every if every.count(x) > 1}):
        bad.append(
            (
                'top-theorems.txt: %s is on more than one line: the audit would '
                'check only the first'
            )
            % n
        )
    for b in bad:
        print('   ' + b)

    def lean_list(name, typ, items, n=100):
        """Returns a Lean definition of a list. On one long list literal Lean's compiler runs out of
        recursion depth (about 2,000 names pass, 2,400 fail), so a longer list is written as chunks
        of at most n entries, each a definition of its own, and their concatenation. A chunk of 100
        lines has room for about 20 names per line; beyond that the audit fails with every verdict
        missing."""
        cs = [items[i : i + n] for i in range(0, len(items), n)] or [[]]
        if len(cs) == 1:
            return 'def %s : List %s := [%s]\n' % (name, typ, ', '.join(cs[0]))
        return ''.join(
            'def %s_%d : List %s := [%s]\n' % (name, i, typ, ', '.join(c)) for i, c in enumerate(cs)
        ) + 'def %s : List %s := %s\n' % (
            name,
            typ,
            ' ++ '.join('%s_%d' % (name, i) for i in range(len(cs))),
        )

    head = 'import Lean\nnamespace LibraryAudit\nopen Lean\n' + lean_list(
        'ourModules', 'Name', [q(m) for m in mods]
    )
    head += lean_list(
        'topTheorems',
        '(Name × Bool × Nat × List Name)',
        [
            '(%s, %s, %d, [%s])'
            % (q(n), 'true' if k is None else 'false', k or 0, ', '.join(q(x) for x in ss))
            for n, k, ss in tops
        ],
    )
    nat = lambda js: '[%s]' % ', '.join(str(j) for j in js)
    head += lean_list(
        'headlines',
        (
            '(Name × List (Name × List Nat) × Name × List (Bool × Name × '
            'List Nat) × List (Option Nat × Name))'
        ),
        [
            '(%s, [%s], %s, [%s], [%s])'
            % (
                q(n),
                ', '.join('(%s, %s)' % (q(c), nat(js)) for c, js in bs),
                q(hd),
                ', '.join(
                    '(%s, %s, %s)' % ('true' if k else 'false', q(c), nat(js)) for k, c, js in zs
                ),
                ', '.join(
                    '(some %d, .anonymous)' % w if isinstance(w, int) else '(none, %s)' % q(w)
                    for w in ws
                ),
            )
            for n, bs, hd, zs, ws in heads
        ],
        20,
    )
    lf = [l.split()[0] for l in data('listing-for.txt')]
    for n in lf:
        if n not in every:
            bad.append('listing-for.txt: %s is not named in top-theorems.txt' % n)
            print('   ' + bad[-1])
    head += lean_list('listFor', 'Name', [q(n) for n in lf if okname.fullmatch(n)])
    counts[
        (
            'theorems with lists and declarations in the listing '
            '(listing-for.txt; 0: all closed ones and all headlines)'
        )
    ] = len(lf)
    pairs = ['(%s, %s)' % (q(x), q(y)) for x, y in allow]
    head += lean_list('choiceAllow', '(Name × Name)', pairs)
    head += (
        'def partSide : Nat := %d\ndef partLimit : Nat := 3600\ndef '
        'companionPart : String := "_unsafe_rec"\ndef companionFloor : '
        'Nat := 1\ndef initTables : List Name := [%s]\n'
    ) % (SIDE, ', '.join(q(x) for x in ('Lean.regularInitAttr', 'Lean.builtinInitAttr')))
    head += 'def nonce : String := "%s"\nend LibraryAudit\n\n' % nonce
    open(fresh('Audit.lean'), 'w', encoding='utf-8').write(head + AUDIT_TEXT)
    verdict(
        'build',
        lrc == 0
        and bool(named)
        and lsorry == 0
        and not unbuilt
        and not left_out
        and build_panics == 0
        and control,
        (
            '"lake build" from scratch: exit %d; it compiled %d files; '
            'messages about sorry: %d; lines that report a panic: %d; files '
            'that must be compiled and were not: %d; of the %d files that only the target %s '
            'reaches, missing from the copy: %d; control run (a one-line '
            'file that panics must make Lean stop): %s'
        )
        % (
            lrc,
            len(named),
            lsorry,
            build_panics,
            len(unbuilt),
            len(THIRD_ONLY),
            'ShapeLines',
            len(left_out),
            'passed' if control else 'FAILED',
        ),
    )
    if lrc or not named:
        verdict('replay', False, 'not run: the build failed')
        verdict('audit', False, 'not run: the build failed')
        tally_counts([], tops, heads, allow)
        return
    if short_of('the largest job of the kernel replay', REPLAY_GIB):
        verdict('replay', False, 'not run: too little memory is free')
        verdict('audit', False, 'not run: too little memory is free')
        tally_counts([], tops, heads, allow)
        return
    seen, skip, rok, rc, A, replay_panics, audit_panics, wide = replay_and_audit(mods, nonce)
    for l in A:
        # printed whole: no part of a line is cut here (the long texts go into the listing)
        print('   AUDIT ' + l)
    # What leanchecker says it replayed, against what was due, by name: a name is a prefix, so a
    # call can bring a module that was not meant, and a module that no name covers is not replayed.
    due = set(mods) - skip - wide
    for what, ns in (
        ('NOT REPLAYED', due - seen),
        ('REPLAYED BUT NOT EXPECTED', seen - due),
    ):
        if ns:
            print(
                '   %s: %d: %s%s'
                % (what, len(ns), ' '.join(sorted(ns)[:12]), ' ...' if len(ns) > 12 else '')
            )
    verdict(
        'replay',
        rok
        and wide == {m for m, _ in wide_modules(mods)}
        and wide_pinned(mods)[0]
        and seen == set(mods) - skip - wide
        and bool(seen)
        and replay_panics == 0,
        (
            'leanchecker replayed %d modules, %d contain only imports, %d of %d went through the '
            'same function by another call with a larger stack (%s), of %d (this library\'s only); '
            'lines that report a panic: %d'
        )
        % (
            len(seen),
            len(skip),
            len(wide),
            len(wide_modules(mods)),
            '; '.join(
                '%s/: %d at --tstack=%d'
                % (lib, len([m for m in wide if m.startswith(lib + '.')]), kb)
                for lib, kb in WIDE_LIBRARIES
            ),
            len(named),
            replay_panics,
        ),
    )
    miss = verdicts_complete(A, tops, heads)
    for x in miss[:12]:
        print('   A VERDICT IS MISSING: ' + x)
    if len(miss) > 12:
        print('   ... and %d more' % (len(miss) - 12))
    verdict(
        'audit',
        rc == 0
        and A.count('ALL PASSED') == 1
        and A[-1:] == ['ALL PASSED']
        and not bad
        and not any(' FAILED' in l.split(':')[0] for l in A)
        and not miss
        and audit_panics == 0,
        '"lake env lean" on the audit: exit %d; it %s; lines that report a panic: %d'
        % (
            rc,
            'ended with ALL PASSED' if A[-1:] == ['ALL PASSED'] else 'did NOT end with ALL PASSED',
            audit_panics,
        ),
    )
    tally_counts(A, tops, heads, allow)
    # take_result has left the file there only if it had the sha256 that the audit printed
    if os.path.isfile('statement-listing.txt'):
        tools['the listing'] = lclib.sha(open('statement-listing.txt', 'rb').read())[:16]
        statements_pinned(open('statement-listing.txt', encoding='utf-8').read())
        print(
            ('   the listing of the compiled definitions on which the top ' 'theorems depend: ')
            + OUT
            + '/statement-listing.txt'
        )
    else:
        print('   the listing was NOT written')
        verdict('audit', False, 'front-statements.txt: not compared: there is no listing')
        notrun.append('the listing (not written)')


t0 = time.time()
print(
    (
        'check.py: the library %s as it was at %s: %d Lean files, sha256 '
        '%s; the copy that is checked: %s%s'
    )
    % (SRC, time.strftime('%H:%M:%S %Z'), len(FILES), DIGEST[:16], OUT + '/tree', SAID),
    flush=True,
)
if ODD:
    print(
        (
            'LEFT OUT: %d Lean files whose paths are not module paths '
            '(letters, digits and _ only), so nothing can import them: %s'
        )
        % (len(ODD), ' '.join(ODD[:8])),
        flush=True,
    )
if UNPRINTABLE:
    print(
        'LEFT OUT: %d files or directories whose names cannot be printed (the step "tree" fails '
        'for them): %s' % (len(UNPRINTABLE), ' '.join(UNPRINTABLE[:8])),
        flush=True,
    )
if WIP:
    print(
        (
            'LEFT OUT, as not part of the library: %d '
            'files named *_wip.lean: %s'
        )
        % (len(WIP), ' '.join(WIP[:12]) + (' ...' if len(WIP) > 12 else '')),
        flush=True,
    )
if ASK:
    print(
        (
            'ASKING FILES: %d: not built, not replayed, not audited: each is run by the command '
            'in its head: %s'
        )
        % (len(ASK), ' '.join(ASK[:12]) + (' ...' if len(ASK) > 12 else '')),
        flush=True,
    )
for s in STEPS:
    if s in only:
        globals()['step_' + s]()
skipped = [s for s in STEPS if s not in only]
# Which modules go by the other call is said in the last lines: the count and the rule. It comes
# from the library's files, so it also stands in a run without the step "build"; the names stand
# whole in the file that the replay writes.
WIDE_NAMED = wide_modules(sorted(lclib.mod_of(r) for r in FILES))
parts = (
    [
        'tree sha256 %s, %d files' % (DIGEST, len(FILES)),
        'checked with: ' + ', '.join('%s %s' % kv for kv in sorted(tools.items())),
    ]
    + ['%d %s' % (v, k) for k, v in counts.items()]
    + (['NOT RUN: ' + ', '.join(notrun + skipped)] if notrun or skipped else [])
    + (['%d asking files, not built, not replayed, not audited' % len(ASK)] if ASK else [])
    + [
        'the kernel replay takes %d modules by another call than leanchecker, with a larger stack: '
        '%s%s (what that call does not do: the comment above WIDE_LIBRARIES in check.py; '
        'scripts/RULES.txt, "One module is replayed by another call")'
        % (
            len(WIDE_NAMED),
            ', '.join(
                'every module of %s/, %d in all'
                % (lib, len([m for m, _ in WIDE_NAMED if m.startswith(lib + '.')]))
                for lib, _ in WIDE_LIBRARIES
            ),
            '; all names: %s/%s' % (OUT, WIDE_NAMES) if WIDE_NAMES in os.listdir(OUT_FD) else '',
        )
    ]
    + (['left out: %d _wip files' % len(WIP)] if WIP else [])
    + (['left out: %d files that nothing can import' % len(ODD)] if ODD else [])
    + (['left out: %d names that cannot be printed' % len(UNPRINTABLE)] if UNPRINTABLE else [])
)
print('%.0f s' % (time.time() - t0))
if 'build' not in only:
    parts += ['this run only read text, and the copy that it checked ' + away(OUT)]
else:
    parts += [
        ('the copy that was checked, with its packages and compiled ' 'files, ') + away(ROOT),
        'the logs and the listing are in ' + OUT,
    ]
print('Particulars of this run:')
for x in parts:
    print('  - ' + x)
if failed:
    print(LAKE_WORDS + 'Check failed: ' + ', '.join(failed) + SAID)
    sys.exit(1)
# A run that passed all four steps says so and exits with status 0; so does a run of some of them
# (--only), whose first word says that it was partial. Neither happens if part of a step was not run
# or had nothing to check (exit status 3), or with Lake files other than the delivered ones
if skipped and not notrun and not LAKE_WORDS:
    print(
        'Partial run passed (%s): only these steps were run%s'
        % (', '.join(s for s in STEPS if s in only), SAID)
    )
    sys.exit(0)
if LAKE_WORDS or skipped or notrun:
    print(LAKE_WORDS + 'Passed so far, and not the full check' + SAID)
    sys.exit(3)
K = counts.get(
    ('declarations that program Lean in the modules below one named ' 'theorem, AT LEAST'), 0
)
# No rule against macros and notations, and no count of them, can be complete (a run_cmd can change
# how a file is read and leave nothing in the compiled file). So the first words always say what the
# result is about
BARE, NCL = counts.get('closed theorems WITHOUT their declarations in the listing', 0), counts.get(
    'of closed theorems', 0
)
BAREH, NH = counts.get('headlines WITHOUT their declarations in the listing', 0), counts.get(
    'of headlines', 0
)
HL = (
    ''
    if not NH or not (BARE or BAREH)
    else (
        ('; it contains the definitions below all %d headlines with named ' 'binders') % NH
        if not BAREH
        else ('; and below ' if BARE else '; but it contains the definitions below ')
        + (
            'only %d of the %d headlines with named binders' % (NH - BAREH, NH)
            if BAREH < NH
            else 'none of the %d headlines with named binders' % NH
        )
    )
)
print(
    (
        'All steps passed: tree, words, imports, build (kernel replay, '
        'audit). This script runs no mutation tests and no second, '
        'independent proof checker (see lean/scripts/README.md). The '
        'result is about the compiled definitions: '
    )
    + (
        'read the listing, not the source'
        if not BARE
        else (
            (
                'the listing contains the definitions below only %d of the %d '
                'closed theorems (listing-for.txt); for those, read it and not '
                'the source'
            )
            % (NCL - BARE, NCL)
            if BARE < NCL
            else (
                'the listing contains the definitions below none of the %d '
                'closed theorems (listing-for.txt names others)'
            )
            % NCL
        )
    )
    + HL
    + (
        '; the kernel replay took %d modules by another call than leanchecker: see the lines above'
        % len(WIDE_NAMED)
    )
    + (
        (' (at least %d declarations program Lean in the modules below ' 'one named theorem)') % K
        if K
        else ''
    )
    + (
        '; no theorem got a verdict on binders or on Classical.choice (every line of '
        'top-theorems.txt says general)'
        if not NCL and not NH
        else ''
    )
    + SAID
)
