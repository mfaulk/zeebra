import struct
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hwcount  # noqa: E402


class HwcountTest(unittest.TestCase):
    def test_attr_is_abi_v7_with_type_config_and_flags_at_their_offsets(self):
        """The attribute is 128 bytes with type, size, config, read_format and flags where the kernel reads them."""
        raw = hwcount.attr(hwcount.RAW, 0x4843)
        self.assertEqual(len(raw), 128)
        kind, size, config, _, _, read_format, flags = struct.unpack_from('IIQQQQQ', raw)
        self.assertEqual((kind, size, config, read_format), (4, 128, 0x4843, 3))
        self.assertTrue(flags & 1 and flags & 2 and flags & (1 << 5) and flags & (1 << 12))
        self.assertFalse(flags & (1 << 4), 'user mode must be counted')

    def test_events_fit_the_five_free_counters(self):
        """No more events than Zen 3's six counters less the NMI watchdog's, so none multiplexes."""
        self.assertLessEqual(len(hwcount.EVENTS), 5)
        self.assertEqual(len({name for name, _, _ in hwcount.EVENTS}), len(hwcount.EVENTS))

    def test_derived_rates_and_missing_denominators(self):
        """IPC and miss rates divide the right counts, and a zero or absent denominator gives None."""
        d = hwcount.derived(dict(cycles=200, instructions=300, l1d_reads=1000, l1d_read_misses=50, fills_dram=5))
        self.assertEqual(d, dict(ipc=1.5, l1d_miss_rate=0.05, dram_per_l1d_miss=0.1))
        d = hwcount.derived(dict(cycles=0, instructions=300))
        self.assertEqual(d, dict(ipc=None, l1d_miss_rate=None, dram_per_l1d_miss=None))

    def test_parse_reads_value_enabled_running(self):
        """A read buffer with TOTAL_TIME_ENABLED | RUNNING is value, enabled, running in that order."""
        self.assertEqual(hwcount.parse(struct.pack('QQQ', 7, 10, 9)), dict(value=7, enabled_ns=10, running_ns=9))


if __name__ == '__main__':
    unittest.main()
