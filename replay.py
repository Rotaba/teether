#!/usr/bin/env python2.7
import curses
import json
import sys
from binascii import unhexlify


def main():
    with open(sys.argv[1]) as infile:
        log = json.load(infile)

    trace = log['structLogs']

    stdscr = curses.initscr()
    curses.noecho()

    for t in trace:
        stdscr.clear()
        stdscr.addstr(0, 0, "PC: %x" % t['pc'])
        stdscr.addstr(0, 20, t['op'], curses.A_BOLD)

        for i, s in enumerate(t['stack'][::-1]):
            stdscr.addstr(5 + i, 10, s)

        if t['memory']:
            total_mem = ''.join(t['memory'])
            lines = [total_mem[i:i + 32] for i in xrange(0, len(total_mem), 32)]
            for i, m in enumerate(lines):
                raw = ''.join(x if 0x20 <= ord(x) < 0x7f else ' ' for x in unhexlify(m))
                m = ' '.join(m[j:j + 2] for j in xrange(0, len(m), 2))
                stdscr.addstr(50 + i, 10, m)
                stdscr.addstr(50 + i, 70, raw)

        stdscr.refresh()
        c = stdscr.getch()
        if c == curses.KEY_EXIT:
            break


if __name__ == '__main__':
    main()
