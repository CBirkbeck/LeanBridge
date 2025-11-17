import * as React from 'react';
const { useState } = React;
import { RpcContext } from '@leanprover/infoview';

export default function LMFDBSearchWidget(props) {
  const initialState = props.initialState || {};
  const [params, setParams] = useState(initialState.searchParams || {
    degree_min: null,
    degree_max: null,
    signature: null,
    disc_abs_min: null,
    disc_abs_max: null,
    disc_sign: null,
    rd_min: null,
    rd_max: null,
    grd_min: null,
    grd_max: null,
    r2_min: null,
    r2_max: null,
    class_number: null,
    narrow_class_number: null,
    class_group: null,
    narrow_class_group: null,
    is_galois: null,
    galois_label: null,
    gal_is_abelian: null,
    gal_is_cyclic: null,
    gal_is_solvable: null,
    num_ram_min: null,
    num_ram_max: null,
    ramps: null,
    unramified_primes: null,
    inessentialp: null,
    cm: null,
    monogenic: null,
    is_minimal_sibling: null,
    regulator_min: null,
    regulator_max: null,
    limit: 50
  });
  const [results, setResults] = useState(initialState.results || []);
  const [selected, setSelected] = useState(initialState.selected || []);
  const [searching, setSearching] = useState(false);
  const [generating, setGenerating] = useState(false);
  const [message, setMessage] = useState(null);
  const [messageType, setMessageType] = useState('info');

  // ... rest of the code stays the same

  const rs = React.useContext(RpcContext);
const updateParam = (field, value) => {
  setParams(prev => {
    const newParams = { ...prev };

    if (value === '' || value === null) {
      newParams[field] = null;
    } else {
      // Convert to appropriate type based on field name
      if (field.includes('_min') || field.includes('_max') ||
          field === 'limit' || field === 'class_number' ||
          field === 'narrow_class_number' || field === 'r2_min' || field === 'r2_max') {
        // These should be numbers
        const num = parseInt(value);
        newParams[field] = isNaN(num) ? null : num;
      } else if (field === 'disc_sign') {
        // Convert disc_sign to integer
        const num = parseInt(value);
        newParams[field] = isNaN(num) ? null : num;
      } else if (field === 'is_galois' || field === 'cm' || field === 'monogenic' ||
                 field === 'gal_is_abelian' || field === 'gal_is_cyclic' ||
                 field === 'gal_is_solvable' || field === 'is_minimal_sibling') {
        // These should be booleans
        newParams[field] = value === 'true';
      } else {
        // Keep as string
        newParams[field] = value;
      }
    }

    return newParams;
  });
};

  const handleSearch = async () => {
    setSearching(true);
    setMessage(null);
    try {
      const searchResults = await rs.call('searchLMFDB', params);
      setResults(searchResults);
      setSelected(new Array(searchResults.length).fill(false));
      setMessage('Found ' + searchResults.length + ' results');
      setMessageType('success');
    } catch (error) {
      setMessage('Search failed: ' + error.message);
      setMessageType('error');
    } finally {
      setSearching(false);
    }
  };

  const handleGenerate = async () => {
    const selectedFields = results.filter((r, i) => selected[i]);
    if (selectedFields.length === 0) {
      setMessage('No fields selected');
      setMessageType('error');
      return;
    }

    setGenerating(true);
    setMessage(null);
    try {
      const result = await rs.call('generateLeanFiles', selectedFields);
      setMessage(result);
      setMessageType('success');
    } catch (error) {
      setMessage('Generation failed: ' + error.message);
      setMessageType('error');
    } finally {
      setGenerating(false);
    }
  };

  const toggleSelect = (index) => {
    setSelected(prev => {
      const newSelected = [...prev];
      newSelected[index] = !newSelected[index];
      return newSelected;
    });
  };

  const selectAll = () => {
    setSelected(new Array(results.length).fill(true));
  };

  const deselectAll = () => {
    setSelected(new Array(results.length).fill(false));
  };

  return React.createElement('div', { style: { padding: '15px', fontFamily: 'sans-serif', maxWidth: '1200px' } },
    React.createElement('h2', { style: { marginTop: 0 } }, 'LMFDB Number Field Search'),

    // Search form
    React.createElement('div', {
      style: {
        border: '1px solid #ccc',
        padding: '15px',
        marginBottom: '15px',
        backgroundColor: '#f9f9f9',
        borderRadius: '4px'
      }
    },
      React.createElement('h3', { style: { marginTop: 0 } }, 'Search Parameters'),

      React.createElement('div', { style: { display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '20px' } },
        // Left column
        React.createElement('div', null,
          createRangeInput('Degree', 'degree_min', 'degree_max', 'e.g. 3', params, updateParam),
          createRangeInput('Discriminant', 'disc_abs_min', 'disc_abs_max', 'e.g. 1000', params, updateParam),
          createDropdown('Disc sign', 'disc_sign', [
            { value: '1', label: 'positive' },
            { value: '-1', label: 'negative' }
          ], params, updateParam),
          createSingleInput('Signature', 'signature', 'e.g. [1,1]', params, updateParam),
          createRangeInput('Root discriminant', 'rd_min', 'rd_max', 'e.g. 1..3', params, updateParam),
          createSingleInput('Galois group', 'galois_label', 'e.g. 8T3', params, updateParam),
          createDropdown('Is Galois', 'is_galois', [
            { value: 'true', label: 'yes' },
            { value: 'false', label: 'no' }
          ], params, updateParam),
          createDropdown('CM field', 'cm', [
            { value: 'true', label: 'yes' },
            { value: 'false', label: 'no' }
          ], params, updateParam)
        ),

        // Right column
        React.createElement('div', null,
          createSingleInput('Class number', 'class_number', 'e.g. 1', params, updateParam),
          createSingleInput('Class group', 'class_group', 'e.g. [1,3]', params, updateParam),
          createRangeInput('Ramified primes', 'num_ram_min', 'num_ram_max', 'count', params, updateParam),
          createSingleInput('Ramified at', 'ramps', 'e.g. 2,3', params, updateParam),
          createDropdown('Monogenic', 'monogenic', [
            { value: 'true', label: 'yes' },
            { value: 'false', label: 'no' }
          ], params, updateParam),
          React.createElement('div', { style: { marginBottom: '8px' } },
            React.createElement('label', { style: { display: 'inline-block', width: '150px', fontSize: '13px' } }, 'Results limit'),
            React.createElement('input', {
              type: 'number',
              value: params.limit || 50,
              onChange: e => updateParam('limit', parseInt(e.target.value) || 50),
              style: { width: '80px', padding: '4px' },
              min: 1,
              max: 1000
            })
          )
        )
      ),

      React.createElement('div', { style: { marginTop: '15px' } },
        React.createElement('button', {
          onClick: handleSearch,
          disabled: searching,
          style: {
            padding: '8px 20px',
            backgroundColor: searching ? '#ccc' : '#4CAF50',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: searching ? 'not-allowed' : 'pointer',
            fontSize: '14px'
          }
        }, searching ? 'Searching...' : 'Search LMFDB')
      )
    ),

    // Message display
    message && React.createElement('div', {
      style: {
        padding: '10px',
        marginBottom: '15px',
        borderRadius: '4px',
        backgroundColor: messageType === 'error' ? '#ffebee' :
                        messageType === 'success' ? '#e8f5e9' : '#e3f2fd',
        color: messageType === 'error' ? '#c62828' :
               messageType === 'success' ? '#2e7d32' : '#1565c0'
      }
    }, message),

    // Results table
    results.length > 0 && React.createElement('div', {
      style: {
        border: '1px solid #ccc',
        padding: '15px',
        backgroundColor: '#fff',
        borderRadius: '4px'
      }
    },
      React.createElement('h3', { style: { marginTop: 0 } },
        'Results (' + results.length + ')',
        React.createElement('button', {
          onClick: selectAll,
          style: { marginLeft: '10px', padding: '4px 8px', fontSize: '12px' }
        }, 'Select All'),
        React.createElement('button', {
          onClick: deselectAll,
          style: { marginLeft: '5px', padding: '4px 8px', fontSize: '12px' }
        }, 'Deselect All')
      ),

      React.createElement('div', {
        style: {
          maxHeight: '400px',
          overflowY: 'auto',
          border: '1px solid #ddd'
        }
      },
        React.createElement('table', {
          style: {
            width: '100%',
            borderCollapse: 'collapse',
            fontSize: '13px'
          }
        },
          React.createElement('thead', {
            style: {
              position: 'sticky',
              top: 0,
              backgroundColor: '#f5f5f5'
            }
          },
            React.createElement('tr', null,
              React.createElement('th', { style: { padding: '8px', textAlign: 'left' } }, 'Select'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'left' } }, 'Label'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'left' } }, 'Coefficients'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'center' } }, 'Class #'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'center' } }, 'Disc'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'center' } }, 'Galois'),
              React.createElement('th', { style: { padding: '8px', textAlign: 'center' } }, 'CM')
            )
          ),
          React.createElement('tbody', null,
            results.map((result, idx) =>
              React.createElement('tr', {
                key: idx,
                style: {
                  backgroundColor: selected[idx] ? '#e3f2fd' : 'white',
                  borderBottom: '1px solid #eee'
                }
              },
                React.createElement('td', { style: { padding: '8px' } },
                  React.createElement('input', {
                    type: 'checkbox',
                    checked: selected[idx],
                    onChange: () => toggleSelect(idx)
                  })
                ),
                React.createElement('td', { style: { padding: '8px', fontFamily: 'monospace' } }, result.label),
                React.createElement('td', { style: { padding: '8px', fontFamily: 'monospace', fontSize: '11px' } }, '[' + result.coeffs + ']'),
                React.createElement('td', { style: { padding: '8px', textAlign: 'center' } }, result.class_number),
                React.createElement('td', { style: { padding: '8px', textAlign: 'center' } },
                  (result.disc_sign === -1 ? '-' : '') + result.disc_abs),
                React.createElement('td', { style: { padding: '8px', textAlign: 'center' } },
                  result.is_galois ? '✓' : '✗'),
                React.createElement('td', { style: { padding: '8px', textAlign: 'center' } },
                  result.cm ? '✓' : '✗')
              )
            )
          )
        )
      ),

      React.createElement('div', { style: { marginTop: '15px' } },
        React.createElement('button', {
          onClick: handleGenerate,
          disabled: generating || selected.filter(Boolean).length === 0,
          style: {
            padding: '8px 20px',
            backgroundColor: (generating || selected.filter(Boolean).length === 0) ? '#ccc' : '#2196F3',
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: (generating || selected.filter(Boolean).length === 0) ? 'not-allowed' : 'pointer',
            fontSize: '14px'
          }
        }, generating ? 'Generating...' : 'Generate Lean Files (' + selected.filter(Boolean).length + ' selected)')
      )
    )
  );
}

// Helper functions
function createRangeInput(label, minField, maxField, placeholder, params, updateParam) {
  return React.createElement('div', { style: { marginBottom: '8px' } },
    React.createElement('label', { style: { display: 'inline-block', width: '150px', fontSize: '13px' } }, label),
    React.createElement('input', {
      type: 'text',
      placeholder: 'min ' + placeholder,
      value: params[minField] || '',
      onChange: e => updateParam(minField, e.target.value),
      style: { width: '70px', marginRight: '5px', padding: '4px' }
    }),
    React.createElement('span', { style: { margin: '0 5px' } }, 'to'),
    React.createElement('input', {
      type: 'text',
      placeholder: 'max ' + placeholder,
      value: params[maxField] || '',
      onChange: e => updateParam(maxField, e.target.value),
      style: { width: '70px', padding: '4px' }
    })
  );
}

function createSingleInput(label, field, placeholder, params, updateParam) {
  return React.createElement('div', { style: { marginBottom: '8px' } },
    React.createElement('label', { style: { display: 'inline-block', width: '150px', fontSize: '13px' } }, label),
    React.createElement('input', {
      type: 'text',
      placeholder: placeholder,
      value: params[field] || '',
      onChange: e => updateParam(field, e.target.value),
      style: { width: '150px', padding: '4px' }
    })
  );
}

function createDropdown(label, field, options, params, updateParam) {
  return React.createElement('div', { style: { marginBottom: '8px' } },
    React.createElement('label', { style: { display: 'inline-block', width: '150px', fontSize: '13px' } }, label),
    React.createElement('select', {
      value: params[field] || '',
      onChange: e => updateParam(field, e.target.value),
      style: { width: '150px', padding: '4px' }
    },
      React.createElement('option', { value: '' }, 'any'),
      ...options.map(opt =>
        React.createElement('option', { key: opt.value, value: opt.value }, opt.label)
      )
    )
  );
}
