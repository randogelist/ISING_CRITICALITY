"""Independent numerical examples and safeguards for literature aggregation."""
from decimal import Decimal as D, localcontext
import unittest

from literature.average import _convert, _mean, calculate


def row(source, p, u, exact=False):
    return dict(source_id=source, p=D(p), u=D(u), exact=exact)


class LiteratureAverageTests(unittest.TestCase):
    def test_hand_computed_inverse_error_weights(self):
        # Errors 1:2 give weights 4:1 and mean (4*0.2+0.6)/5 = 0.28.
        result = _mean([row('A', '0.2', '0.01'), row('B', '0.6', '0.02')])
        self.assertEqual(result['p_mean'], D('0.28'))
        self.assertEqual([c['normalized_weight'] for c in result['contributions']],
                         [D('0.8'), D('0.2')])
        # Changing all quoted errors by one common factor cannot change the mean.
        scaled = _mean([row('A', '0.2', '0.1'), row('B', '0.6', '0.2')])
        self.assertEqual(result['p_mean'], scaled['p_mean'])

    def test_exact_precedence(self):
        result = _mean([row('estimate', '0.51', '0.001'),
                        row('theorem', '0.5', '0', True)])
        self.assertEqual(result['status'], 'exact')
        self.assertEqual(result['p_mean'], D('0.5'))
        self.assertEqual(result['source_count'], 1)

    def test_duplicate_source_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate source'):
            _mean([row('paper', '0.2', '0.01'), row('paper', '0.3', '0.02')])

    def test_coupling_conventions(self):
        with localcontext() as context:
            context.prec = 50
            self.assertEqual(_convert('K_Ising', D('0.2')),
                             _convert('K_Potts', D('0.4')))
            self.assertEqual(_convert('K_Ising', D('0.2')),
                             _convert('T_Ising', D('5')))
            self.assertEqual(_convert('beta_BB', D('0.2')),
                             _convert('T_Potts', D('2.5')))
            self.assertLess(_convert('T_Ising', D('5.1')),
                            _convert('T_Ising', D('4.9')))

    def test_real_policy_and_sensitivities(self):
        results = calculate()
        self.assertEqual(len(results), 30)
        self.assertEqual(results[2, 11]['status'], 'missing')
        self.assertIsNone(results[2, 11]['p_mean'])
        potts = results[3, 3]
        self.assertEqual(potts['source_count'], 2)
        self.assertEqual({r['source_id'] for r in potts['contributions']},
                         {'JV1997', 'BB2007'})
        self.assertEqual({r['source_id'] for r in potts['excluded']},
                         {'BB2007', 'W2014'})
        substitute = potts['sensitivity_alternatives'][0]
        self.assertEqual(substitute['name'], 'BB2007_eq24_substitution')
        self.assertEqual(substitute['source_count'], 2)
        self.assertLess(substitute['p_mean'], potts['p_mean'])
        ising = results[2, 3]
        hotrg = next(r for r in ising['contributions'] if r['source_id'] == 'W2014')
        self.assertGreater(hotrg['normalized_weight'], D('0.99'))
        mc = next(r for r in ising['contributions'] if r['source_id'] == 'FXL2018')
        omitted = next(r for r in ising['leave_one_source_out']
                       if r['omitted_source_id'] == 'W2014')
        self.assertEqual(omitted['p_mean'], mc['p_value'])
        self.assertEqual(omitted['source_count'], 1)
        self.assertEqual(results[1, 3]['p_mean'], D('0.248811835'))


if __name__ == '__main__':
    unittest.main()
